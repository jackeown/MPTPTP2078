%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0bMAAucipC

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:20 EST 2020

% Result     : Theorem 43.42s
% Output     : Refutation 43.42s
% Verified   : 
% Statistics : Number of formulae       :  146 (1980 expanded)
%              Number of leaves         :   37 ( 578 expanded)
%              Depth                    :   31
%              Number of atoms          : 1039 (27944 expanded)
%              Number of equality atoms :   88 (1955 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X20 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('13',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_B )
      | ( X41
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X41 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

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

thf('34',plain,(
    ! [X11: $i,X13: $i,X15: $i,X16: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X11 ) )
      | ( X15
       != ( k1_funct_1 @ X11 @ X16 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('35',plain,(
    ! [X11: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X16 ) @ ( k2_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['36','37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

thf('49',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['14','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('52',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('53',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('54',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ k1_xboole_0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('57',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('58',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 != k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('68',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('71',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('72',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('74',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','76'])).

thf('78',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('79',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf('80',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['75'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['75'])).

thf('83',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('85',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['75'])).

thf('86',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('88',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('91',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['89','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['92'])).

thf('94',plain,(
    zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['88','93'])).

thf('95',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['83','94'])).

thf('96',plain,(
    ! [X11: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X16 ) @ ( k2_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ k1_xboole_0 ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['77','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('105',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['50','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0bMAAucipC
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 43.42/43.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 43.42/43.69  % Solved by: fo/fo7.sh
% 43.42/43.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 43.42/43.69  % done 8592 iterations in 43.233s
% 43.42/43.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 43.42/43.69  % SZS output start Refutation
% 43.42/43.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 43.42/43.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 43.42/43.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 43.42/43.69  thf(sk_A_type, type, sk_A: $i).
% 43.42/43.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 43.42/43.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 43.42/43.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 43.42/43.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 43.42/43.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 43.42/43.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 43.42/43.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 43.42/43.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 43.42/43.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 43.42/43.69  thf(sk_E_type, type, sk_E: $i > $i).
% 43.42/43.69  thf(sk_B_type, type, sk_B: $i).
% 43.42/43.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 43.42/43.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 43.42/43.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 43.42/43.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 43.42/43.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 43.42/43.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 43.42/43.69  thf(t16_funct_2, conjecture,
% 43.42/43.69    (![A:$i,B:$i,C:$i]:
% 43.42/43.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 43.42/43.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.42/43.69       ( ( ![D:$i]:
% 43.42/43.69           ( ~( ( r2_hidden @ D @ B ) & 
% 43.42/43.69                ( ![E:$i]:
% 43.42/43.69                  ( ~( ( r2_hidden @ E @ A ) & 
% 43.42/43.69                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 43.42/43.69         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 43.42/43.69  thf(zf_stmt_0, negated_conjecture,
% 43.42/43.69    (~( ![A:$i,B:$i,C:$i]:
% 43.42/43.69        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 43.42/43.69            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.42/43.69          ( ( ![D:$i]:
% 43.42/43.69              ( ~( ( r2_hidden @ D @ B ) & 
% 43.42/43.69                   ( ![E:$i]:
% 43.42/43.69                     ( ~( ( r2_hidden @ E @ A ) & 
% 43.42/43.69                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 43.42/43.69            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 43.42/43.69    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 43.42/43.69  thf('0', plain,
% 43.42/43.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf(dt_k2_relset_1, axiom,
% 43.42/43.69    (![A:$i,B:$i,C:$i]:
% 43.42/43.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.42/43.69       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 43.42/43.69  thf('1', plain,
% 43.42/43.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 43.42/43.69         ((m1_subset_1 @ (k2_relset_1 @ X20 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 43.42/43.69          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 43.42/43.69      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 43.42/43.69  thf('2', plain,
% 43.42/43.69      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 43.42/43.69        (k1_zfmisc_1 @ sk_B))),
% 43.42/43.69      inference('sup-', [status(thm)], ['0', '1'])).
% 43.42/43.69  thf('3', plain,
% 43.42/43.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf(redefinition_k2_relset_1, axiom,
% 43.42/43.69    (![A:$i,B:$i,C:$i]:
% 43.42/43.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.42/43.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 43.42/43.69  thf('4', plain,
% 43.42/43.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 43.42/43.69         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 43.42/43.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 43.42/43.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 43.42/43.69  thf('5', plain,
% 43.42/43.69      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 43.42/43.69      inference('sup-', [status(thm)], ['3', '4'])).
% 43.42/43.69  thf('6', plain,
% 43.42/43.69      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 43.42/43.69      inference('demod', [status(thm)], ['2', '5'])).
% 43.42/43.69  thf(t3_subset, axiom,
% 43.42/43.69    (![A:$i,B:$i]:
% 43.42/43.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 43.42/43.69  thf('7', plain,
% 43.42/43.69      (![X7 : $i, X8 : $i]:
% 43.42/43.69         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 43.42/43.69      inference('cnf', [status(esa)], [t3_subset])).
% 43.42/43.69  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 43.42/43.69      inference('sup-', [status(thm)], ['6', '7'])).
% 43.42/43.69  thf(d10_xboole_0, axiom,
% 43.42/43.69    (![A:$i,B:$i]:
% 43.42/43.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 43.42/43.69  thf('9', plain,
% 43.42/43.69      (![X4 : $i, X6 : $i]:
% 43.42/43.69         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 43.42/43.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 43.42/43.69  thf('10', plain,
% 43.42/43.69      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 43.42/43.69        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('sup-', [status(thm)], ['8', '9'])).
% 43.42/43.69  thf('11', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf('12', plain,
% 43.42/43.69      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 43.42/43.69      inference('sup-', [status(thm)], ['3', '4'])).
% 43.42/43.69  thf('13', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 43.42/43.69      inference('demod', [status(thm)], ['11', '12'])).
% 43.42/43.69  thf('14', plain, (~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 43.42/43.69      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 43.42/43.69  thf(d3_tarski, axiom,
% 43.42/43.69    (![A:$i,B:$i]:
% 43.42/43.69     ( ( r1_tarski @ A @ B ) <=>
% 43.42/43.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 43.42/43.69  thf('15', plain,
% 43.42/43.69      (![X1 : $i, X3 : $i]:
% 43.42/43.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 43.42/43.69      inference('cnf', [status(esa)], [d3_tarski])).
% 43.42/43.69  thf('16', plain,
% 43.42/43.69      (![X41 : $i]:
% 43.42/43.69         (~ (r2_hidden @ X41 @ sk_B)
% 43.42/43.69          | ((X41) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X41))))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf('17', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r1_tarski @ sk_B @ X0)
% 43.42/43.69          | ((sk_C @ X0 @ sk_B)
% 43.42/43.69              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 43.42/43.69      inference('sup-', [status(thm)], ['15', '16'])).
% 43.42/43.69  thf('18', plain,
% 43.42/43.69      (![X1 : $i, X3 : $i]:
% 43.42/43.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 43.42/43.69      inference('cnf', [status(esa)], [d3_tarski])).
% 43.42/43.69  thf('19', plain,
% 43.42/43.69      (![X41 : $i]:
% 43.42/43.69         (~ (r2_hidden @ X41 @ sk_B) | (r2_hidden @ (sk_E @ X41) @ sk_A))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf('20', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r1_tarski @ sk_B @ X0)
% 43.42/43.69          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 43.42/43.69      inference('sup-', [status(thm)], ['18', '19'])).
% 43.42/43.69  thf(d1_funct_2, axiom,
% 43.42/43.69    (![A:$i,B:$i,C:$i]:
% 43.42/43.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.42/43.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 43.42/43.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 43.42/43.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 43.42/43.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 43.42/43.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 43.42/43.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 43.42/43.69  thf(zf_stmt_1, axiom,
% 43.42/43.69    (![B:$i,A:$i]:
% 43.42/43.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 43.42/43.69       ( zip_tseitin_0 @ B @ A ) ))).
% 43.42/43.69  thf('21', plain,
% 43.42/43.69      (![X29 : $i, X30 : $i]:
% 43.42/43.69         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 43.42/43.69  thf('22', plain,
% 43.42/43.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 43.42/43.69  thf(zf_stmt_3, axiom,
% 43.42/43.69    (![C:$i,B:$i,A:$i]:
% 43.42/43.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 43.42/43.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 43.42/43.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 43.42/43.69  thf(zf_stmt_5, axiom,
% 43.42/43.69    (![A:$i,B:$i,C:$i]:
% 43.42/43.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.42/43.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 43.42/43.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 43.42/43.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 43.42/43.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 43.42/43.69  thf('23', plain,
% 43.42/43.69      (![X34 : $i, X35 : $i, X36 : $i]:
% 43.42/43.69         (~ (zip_tseitin_0 @ X34 @ X35)
% 43.42/43.69          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 43.42/43.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 43.42/43.69  thf('24', plain,
% 43.42/43.69      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 43.42/43.69        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 43.42/43.69      inference('sup-', [status(thm)], ['22', '23'])).
% 43.42/43.69  thf('25', plain,
% 43.42/43.69      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 43.42/43.69      inference('sup-', [status(thm)], ['21', '24'])).
% 43.42/43.69  thf('26', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf('27', plain,
% 43.42/43.69      (![X31 : $i, X32 : $i, X33 : $i]:
% 43.42/43.69         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 43.42/43.69          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 43.42/43.69          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 43.42/43.69  thf('28', plain,
% 43.42/43.69      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 43.42/43.69        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 43.42/43.69      inference('sup-', [status(thm)], ['26', '27'])).
% 43.42/43.69  thf('29', plain,
% 43.42/43.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf(redefinition_k1_relset_1, axiom,
% 43.42/43.69    (![A:$i,B:$i,C:$i]:
% 43.42/43.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.42/43.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 43.42/43.69  thf('30', plain,
% 43.42/43.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 43.42/43.69         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 43.42/43.69          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 43.42/43.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 43.42/43.69  thf('31', plain,
% 43.42/43.69      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 43.42/43.69      inference('sup-', [status(thm)], ['29', '30'])).
% 43.42/43.69  thf('32', plain,
% 43.42/43.69      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 43.42/43.69        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('demod', [status(thm)], ['28', '31'])).
% 43.42/43.69  thf('33', plain,
% 43.42/43.69      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('sup-', [status(thm)], ['25', '32'])).
% 43.42/43.69  thf(d5_funct_1, axiom,
% 43.42/43.69    (![A:$i]:
% 43.42/43.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 43.42/43.69       ( ![B:$i]:
% 43.42/43.69         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 43.42/43.69           ( ![C:$i]:
% 43.42/43.69             ( ( r2_hidden @ C @ B ) <=>
% 43.42/43.69               ( ?[D:$i]:
% 43.42/43.69                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 43.42/43.69                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 43.42/43.69  thf('34', plain,
% 43.42/43.69      (![X11 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 43.42/43.69         (((X13) != (k2_relat_1 @ X11))
% 43.42/43.69          | (r2_hidden @ X15 @ X13)
% 43.42/43.69          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X11))
% 43.42/43.69          | ((X15) != (k1_funct_1 @ X11 @ X16))
% 43.42/43.69          | ~ (v1_funct_1 @ X11)
% 43.42/43.69          | ~ (v1_relat_1 @ X11))),
% 43.42/43.69      inference('cnf', [status(esa)], [d5_funct_1])).
% 43.42/43.69  thf('35', plain,
% 43.42/43.69      (![X11 : $i, X16 : $i]:
% 43.42/43.69         (~ (v1_relat_1 @ X11)
% 43.42/43.69          | ~ (v1_funct_1 @ X11)
% 43.42/43.69          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X11))
% 43.42/43.69          | (r2_hidden @ (k1_funct_1 @ X11 @ X16) @ (k2_relat_1 @ X11)))),
% 43.42/43.69      inference('simplify', [status(thm)], ['34'])).
% 43.42/43.69  thf('36', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         (~ (r2_hidden @ X0 @ sk_A)
% 43.42/43.69          | ((sk_B) = (k1_xboole_0))
% 43.42/43.69          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 43.42/43.69          | ~ (v1_funct_1 @ sk_C_2)
% 43.42/43.69          | ~ (v1_relat_1 @ sk_C_2))),
% 43.42/43.69      inference('sup-', [status(thm)], ['33', '35'])).
% 43.42/43.69  thf('37', plain, ((v1_funct_1 @ sk_C_2)),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf('38', plain,
% 43.42/43.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf(cc1_relset_1, axiom,
% 43.42/43.69    (![A:$i,B:$i,C:$i]:
% 43.42/43.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.42/43.69       ( v1_relat_1 @ C ) ))).
% 43.42/43.69  thf('39', plain,
% 43.42/43.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 43.42/43.69         ((v1_relat_1 @ X17)
% 43.42/43.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 43.42/43.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 43.42/43.69  thf('40', plain, ((v1_relat_1 @ sk_C_2)),
% 43.42/43.69      inference('sup-', [status(thm)], ['38', '39'])).
% 43.42/43.69  thf('41', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         (~ (r2_hidden @ X0 @ sk_A)
% 43.42/43.69          | ((sk_B) = (k1_xboole_0))
% 43.42/43.69          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('demod', [status(thm)], ['36', '37', '40'])).
% 43.42/43.69  thf('42', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r1_tarski @ sk_B @ X0)
% 43.42/43.69          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 43.42/43.69             (k2_relat_1 @ sk_C_2))
% 43.42/43.69          | ((sk_B) = (k1_xboole_0)))),
% 43.42/43.69      inference('sup-', [status(thm)], ['20', '41'])).
% 43.42/43.69  thf('43', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 43.42/43.69          | (r1_tarski @ sk_B @ X0)
% 43.42/43.69          | ((sk_B) = (k1_xboole_0))
% 43.42/43.69          | (r1_tarski @ sk_B @ X0))),
% 43.42/43.69      inference('sup+', [status(thm)], ['17', '42'])).
% 43.42/43.69  thf('44', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         (((sk_B) = (k1_xboole_0))
% 43.42/43.69          | (r1_tarski @ sk_B @ X0)
% 43.42/43.69          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('simplify', [status(thm)], ['43'])).
% 43.42/43.69  thf('45', plain,
% 43.42/43.69      (![X1 : $i, X3 : $i]:
% 43.42/43.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 43.42/43.69      inference('cnf', [status(esa)], [d3_tarski])).
% 43.42/43.69  thf('46', plain,
% 43.42/43.69      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 43.42/43.69        | ((sk_B) = (k1_xboole_0))
% 43.42/43.69        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('sup-', [status(thm)], ['44', '45'])).
% 43.42/43.69  thf('47', plain,
% 43.42/43.69      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('simplify', [status(thm)], ['46'])).
% 43.42/43.69  thf('48', plain, (~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 43.42/43.69      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 43.42/43.69  thf('49', plain, (((sk_B) = (k1_xboole_0))),
% 43.42/43.69      inference('clc', [status(thm)], ['47', '48'])).
% 43.42/43.69  thf('50', plain, (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_C_2))),
% 43.42/43.69      inference('demod', [status(thm)], ['14', '49'])).
% 43.42/43.69  thf('51', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r1_tarski @ sk_B @ X0)
% 43.42/43.69          | ((sk_C @ X0 @ sk_B)
% 43.42/43.69              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 43.42/43.69      inference('sup-', [status(thm)], ['15', '16'])).
% 43.42/43.69  thf('52', plain, (((sk_B) = (k1_xboole_0))),
% 43.42/43.69      inference('clc', [status(thm)], ['47', '48'])).
% 43.42/43.69  thf('53', plain, (((sk_B) = (k1_xboole_0))),
% 43.42/43.69      inference('clc', [status(thm)], ['47', '48'])).
% 43.42/43.69  thf('54', plain, (((sk_B) = (k1_xboole_0))),
% 43.42/43.69      inference('clc', [status(thm)], ['47', '48'])).
% 43.42/43.69  thf('55', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r1_tarski @ k1_xboole_0 @ X0)
% 43.42/43.69          | ((sk_C @ X0 @ k1_xboole_0)
% 43.42/43.69              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ k1_xboole_0)))))),
% 43.42/43.69      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 43.42/43.69  thf('56', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r1_tarski @ sk_B @ X0)
% 43.42/43.69          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 43.42/43.69      inference('sup-', [status(thm)], ['18', '19'])).
% 43.42/43.69  thf('57', plain, (((sk_B) = (k1_xboole_0))),
% 43.42/43.69      inference('clc', [status(thm)], ['47', '48'])).
% 43.42/43.69  thf('58', plain, (((sk_B) = (k1_xboole_0))),
% 43.42/43.69      inference('clc', [status(thm)], ['47', '48'])).
% 43.42/43.69  thf('59', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r1_tarski @ k1_xboole_0 @ X0)
% 43.42/43.69          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ k1_xboole_0)) @ sk_A))),
% 43.42/43.69      inference('demod', [status(thm)], ['56', '57', '58'])).
% 43.42/43.69  thf('60', plain,
% 43.42/43.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf('61', plain, (((sk_B) = (k1_xboole_0))),
% 43.42/43.69      inference('clc', [status(thm)], ['47', '48'])).
% 43.42/43.69  thf('62', plain,
% 43.42/43.69      ((m1_subset_1 @ sk_C_2 @ 
% 43.42/43.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 43.42/43.69      inference('demod', [status(thm)], ['60', '61'])).
% 43.42/43.69  thf('63', plain,
% 43.42/43.69      (![X34 : $i, X35 : $i, X36 : $i]:
% 43.42/43.69         (((X34) != (k1_xboole_0))
% 43.42/43.69          | ((X35) = (k1_xboole_0))
% 43.42/43.69          | ((X36) = (k1_xboole_0))
% 43.42/43.69          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 43.42/43.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 43.42/43.69  thf('64', plain,
% 43.42/43.69      (![X35 : $i, X36 : $i]:
% 43.42/43.69         (~ (m1_subset_1 @ X36 @ 
% 43.42/43.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ k1_xboole_0)))
% 43.42/43.69          | ~ (v1_funct_2 @ X36 @ X35 @ k1_xboole_0)
% 43.42/43.69          | ((X36) = (k1_xboole_0))
% 43.42/43.69          | ((X35) = (k1_xboole_0)))),
% 43.42/43.69      inference('simplify', [status(thm)], ['63'])).
% 43.42/43.69  thf('65', plain,
% 43.42/43.69      ((((sk_A) = (k1_xboole_0))
% 43.42/43.69        | ((sk_C_2) = (k1_xboole_0))
% 43.42/43.69        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0))),
% 43.42/43.69      inference('sup-', [status(thm)], ['62', '64'])).
% 43.42/43.69  thf('66', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf('67', plain, (((sk_B) = (k1_xboole_0))),
% 43.42/43.69      inference('clc', [status(thm)], ['47', '48'])).
% 43.42/43.69  thf('68', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0)),
% 43.42/43.69      inference('demod', [status(thm)], ['66', '67'])).
% 43.42/43.69  thf('69', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 43.42/43.69      inference('demod', [status(thm)], ['65', '68'])).
% 43.42/43.69  thf('70', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 43.42/43.69      inference('demod', [status(thm)], ['11', '12'])).
% 43.42/43.69  thf('71', plain, (((sk_B) = (k1_xboole_0))),
% 43.42/43.69      inference('clc', [status(thm)], ['47', '48'])).
% 43.42/43.69  thf('72', plain, (((k2_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 43.42/43.69      inference('demod', [status(thm)], ['70', '71'])).
% 43.42/43.69  thf('73', plain,
% 43.42/43.69      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 43.42/43.69        | ((sk_A) = (k1_xboole_0)))),
% 43.42/43.69      inference('sup-', [status(thm)], ['69', '72'])).
% 43.42/43.69  thf(t60_relat_1, axiom,
% 43.42/43.69    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 43.42/43.69     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 43.42/43.69  thf('74', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 43.42/43.69      inference('cnf', [status(esa)], [t60_relat_1])).
% 43.42/43.69  thf('75', plain,
% 43.42/43.69      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 43.42/43.69      inference('demod', [status(thm)], ['73', '74'])).
% 43.42/43.69  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 43.42/43.69      inference('simplify', [status(thm)], ['75'])).
% 43.42/43.69  thf('77', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r1_tarski @ k1_xboole_0 @ X0)
% 43.42/43.69          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ k1_xboole_0)) @ k1_xboole_0))),
% 43.42/43.69      inference('demod', [status(thm)], ['59', '76'])).
% 43.42/43.69  thf('78', plain,
% 43.42/43.69      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 43.42/43.69        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('demod', [status(thm)], ['28', '31'])).
% 43.42/43.69  thf('79', plain, (((sk_B) = (k1_xboole_0))),
% 43.42/43.69      inference('clc', [status(thm)], ['47', '48'])).
% 43.42/43.69  thf('80', plain,
% 43.42/43.69      ((~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A)
% 43.42/43.69        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('demod', [status(thm)], ['78', '79'])).
% 43.42/43.69  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 43.42/43.69      inference('simplify', [status(thm)], ['75'])).
% 43.42/43.69  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 43.42/43.69      inference('simplify', [status(thm)], ['75'])).
% 43.42/43.69  thf('83', plain,
% 43.42/43.69      ((~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 43.42/43.69        | ((k1_xboole_0) = (k1_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('demod', [status(thm)], ['80', '81', '82'])).
% 43.42/43.69  thf('84', plain,
% 43.42/43.69      ((m1_subset_1 @ sk_C_2 @ 
% 43.42/43.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 43.42/43.69      inference('demod', [status(thm)], ['60', '61'])).
% 43.42/43.69  thf('85', plain, (((sk_A) = (k1_xboole_0))),
% 43.42/43.69      inference('simplify', [status(thm)], ['75'])).
% 43.42/43.69  thf('86', plain,
% 43.42/43.69      ((m1_subset_1 @ sk_C_2 @ 
% 43.42/43.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 43.42/43.69      inference('demod', [status(thm)], ['84', '85'])).
% 43.42/43.69  thf('87', plain,
% 43.42/43.69      (![X34 : $i, X35 : $i, X36 : $i]:
% 43.42/43.69         (~ (zip_tseitin_0 @ X34 @ X35)
% 43.42/43.69          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 43.42/43.69          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 43.42/43.69  thf('88', plain,
% 43.42/43.69      (((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 43.42/43.69        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 43.42/43.69      inference('sup-', [status(thm)], ['86', '87'])).
% 43.42/43.69  thf('89', plain,
% 43.42/43.69      (![X29 : $i, X30 : $i]:
% 43.42/43.69         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 43.42/43.69  thf('90', plain,
% 43.42/43.69      (![X29 : $i, X30 : $i]:
% 43.42/43.69         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 43.42/43.69  thf('91', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 43.42/43.69      inference('simplify', [status(thm)], ['90'])).
% 43.42/43.69  thf('92', plain,
% 43.42/43.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.42/43.69         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 43.42/43.69      inference('sup+', [status(thm)], ['89', '91'])).
% 43.42/43.69  thf('93', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 43.42/43.69      inference('eq_fact', [status(thm)], ['92'])).
% 43.42/43.69  thf('94', plain, ((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)),
% 43.42/43.69      inference('demod', [status(thm)], ['88', '93'])).
% 43.42/43.69  thf('95', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C_2))),
% 43.42/43.69      inference('demod', [status(thm)], ['83', '94'])).
% 43.42/43.69  thf('96', plain,
% 43.42/43.69      (![X11 : $i, X16 : $i]:
% 43.42/43.69         (~ (v1_relat_1 @ X11)
% 43.42/43.69          | ~ (v1_funct_1 @ X11)
% 43.42/43.69          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X11))
% 43.42/43.69          | (r2_hidden @ (k1_funct_1 @ X11 @ X16) @ (k2_relat_1 @ X11)))),
% 43.42/43.69      inference('simplify', [status(thm)], ['34'])).
% 43.42/43.69  thf('97', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 43.42/43.69          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 43.42/43.69          | ~ (v1_funct_1 @ sk_C_2)
% 43.42/43.69          | ~ (v1_relat_1 @ sk_C_2))),
% 43.42/43.69      inference('sup-', [status(thm)], ['95', '96'])).
% 43.42/43.69  thf('98', plain, ((v1_funct_1 @ sk_C_2)),
% 43.42/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.42/43.69  thf('99', plain, ((v1_relat_1 @ sk_C_2)),
% 43.42/43.69      inference('sup-', [status(thm)], ['38', '39'])).
% 43.42/43.69  thf('100', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 43.42/43.69          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('demod', [status(thm)], ['97', '98', '99'])).
% 43.42/43.69  thf('101', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r1_tarski @ k1_xboole_0 @ X0)
% 43.42/43.69          | (r2_hidden @ 
% 43.42/43.69             (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ k1_xboole_0))) @ 
% 43.42/43.69             (k2_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('sup-', [status(thm)], ['77', '100'])).
% 43.42/43.69  thf('102', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k2_relat_1 @ sk_C_2))
% 43.42/43.69          | (r1_tarski @ k1_xboole_0 @ X0)
% 43.42/43.69          | (r1_tarski @ k1_xboole_0 @ X0))),
% 43.42/43.69      inference('sup+', [status(thm)], ['55', '101'])).
% 43.42/43.69  thf('103', plain,
% 43.42/43.69      (![X0 : $i]:
% 43.42/43.69         ((r1_tarski @ k1_xboole_0 @ X0)
% 43.42/43.69          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k2_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('simplify', [status(thm)], ['102'])).
% 43.42/43.69  thf('104', plain,
% 43.42/43.69      (![X1 : $i, X3 : $i]:
% 43.42/43.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 43.42/43.69      inference('cnf', [status(esa)], [d3_tarski])).
% 43.42/43.69  thf('105', plain,
% 43.42/43.69      (((r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_C_2))
% 43.42/43.69        | (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_C_2)))),
% 43.42/43.69      inference('sup-', [status(thm)], ['103', '104'])).
% 43.42/43.69  thf('106', plain, ((r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_C_2))),
% 43.42/43.69      inference('simplify', [status(thm)], ['105'])).
% 43.42/43.69  thf('107', plain, ($false), inference('demod', [status(thm)], ['50', '106'])).
% 43.42/43.69  
% 43.42/43.69  % SZS output end Refutation
% 43.42/43.69  
% 43.42/43.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
