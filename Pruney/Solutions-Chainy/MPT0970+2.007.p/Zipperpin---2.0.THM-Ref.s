%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pIYG1gUViI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:17 EST 2020

% Result     : Theorem 7.28s
% Output     : Refutation 7.28s
% Verified   : 
% Statistics : Number of formulae       :  146 (1636 expanded)
%              Number of leaves         :   40 ( 481 expanded)
%              Depth                    :   29
%              Number of atoms          : 1008 (22775 expanded)
%              Number of equality atoms :  106 (1646 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

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
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
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

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('5',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( X37
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X37 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('15',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

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

thf('21',plain,(
    ! [X11: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X16 ) @ ( k2_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['22','23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B )
    | ( ( k2_relat_1 @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('38',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = sk_B ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['6','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['43','48'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 != k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['43','48'])).

thf('59',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['44','47'])).

thf('62',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['43','48'])).

thf('63',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('65',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf('69',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['50','67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('77',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['75','77'])).

thf('79',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('83',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X9 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( ( k2_relat_1 @ sk_C_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k2_relat_1 @ sk_C_2 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_2 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['44','47'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != sk_B )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['43','48'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf('95',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['74','95'])).

thf('97',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['69','96'])).

thf('98',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X9 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('99',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('101',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pIYG1gUViI
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.28/7.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.28/7.46  % Solved by: fo/fo7.sh
% 7.28/7.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.28/7.46  % done 4299 iterations in 7.001s
% 7.28/7.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.28/7.46  % SZS output start Refutation
% 7.28/7.46  thf(sk_B_type, type, sk_B: $i).
% 7.28/7.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.28/7.46  thf(sk_C_2_type, type, sk_C_2: $i).
% 7.28/7.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.28/7.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.28/7.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 7.28/7.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.28/7.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.28/7.46  thf(sk_A_type, type, sk_A: $i).
% 7.28/7.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.28/7.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.28/7.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 7.28/7.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.28/7.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.28/7.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 7.28/7.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 7.28/7.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.28/7.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 7.28/7.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.28/7.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.28/7.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.28/7.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.28/7.46  thf(sk_E_type, type, sk_E: $i > $i).
% 7.28/7.46  thf(t16_funct_2, conjecture,
% 7.28/7.46    (![A:$i,B:$i,C:$i]:
% 7.28/7.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.28/7.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.28/7.46       ( ( ![D:$i]:
% 7.28/7.46           ( ~( ( r2_hidden @ D @ B ) & 
% 7.28/7.46                ( ![E:$i]:
% 7.28/7.46                  ( ~( ( r2_hidden @ E @ A ) & 
% 7.28/7.46                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 7.28/7.46         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 7.28/7.46  thf(zf_stmt_0, negated_conjecture,
% 7.28/7.46    (~( ![A:$i,B:$i,C:$i]:
% 7.28/7.46        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.28/7.46            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.28/7.46          ( ( ![D:$i]:
% 7.28/7.46              ( ~( ( r2_hidden @ D @ B ) & 
% 7.28/7.46                   ( ![E:$i]:
% 7.28/7.46                     ( ~( ( r2_hidden @ E @ A ) & 
% 7.28/7.46                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 7.28/7.46            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 7.28/7.46    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 7.28/7.46  thf('0', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf(d1_funct_2, axiom,
% 7.28/7.46    (![A:$i,B:$i,C:$i]:
% 7.28/7.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.28/7.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.28/7.46           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 7.28/7.46             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 7.28/7.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.28/7.46           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 7.28/7.46             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 7.28/7.46  thf(zf_stmt_1, axiom,
% 7.28/7.46    (![C:$i,B:$i,A:$i]:
% 7.28/7.46     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 7.28/7.46       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 7.28/7.46  thf('1', plain,
% 7.28/7.46      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.28/7.46         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 7.28/7.46          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 7.28/7.46          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.28/7.46  thf('2', plain,
% 7.28/7.46      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.28/7.46        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 7.28/7.46      inference('sup-', [status(thm)], ['0', '1'])).
% 7.28/7.46  thf('3', plain,
% 7.28/7.46      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf(redefinition_k1_relset_1, axiom,
% 7.28/7.46    (![A:$i,B:$i,C:$i]:
% 7.28/7.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.28/7.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 7.28/7.46  thf('4', plain,
% 7.28/7.46      (![X23 : $i, X24 : $i, X25 : $i]:
% 7.28/7.46         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 7.28/7.46          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 7.28/7.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.28/7.46  thf('5', plain,
% 7.28/7.46      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 7.28/7.46      inference('sup-', [status(thm)], ['3', '4'])).
% 7.28/7.46  thf('6', plain,
% 7.28/7.46      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.28/7.46        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('demod', [status(thm)], ['2', '5'])).
% 7.28/7.46  thf(d3_tarski, axiom,
% 7.28/7.46    (![A:$i,B:$i]:
% 7.28/7.46     ( ( r1_tarski @ A @ B ) <=>
% 7.28/7.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.28/7.46  thf('7', plain,
% 7.28/7.46      (![X1 : $i, X3 : $i]:
% 7.28/7.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.28/7.46      inference('cnf', [status(esa)], [d3_tarski])).
% 7.28/7.46  thf('8', plain,
% 7.28/7.46      (![X37 : $i]:
% 7.28/7.46         (~ (r2_hidden @ X37 @ sk_B)
% 7.28/7.46          | ((X37) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X37))))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf('9', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         ((r1_tarski @ sk_B @ X0)
% 7.28/7.46          | ((sk_C @ X0 @ sk_B)
% 7.28/7.46              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 7.28/7.46      inference('sup-', [status(thm)], ['7', '8'])).
% 7.28/7.46  thf('10', plain,
% 7.28/7.46      (![X1 : $i, X3 : $i]:
% 7.28/7.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.28/7.46      inference('cnf', [status(esa)], [d3_tarski])).
% 7.28/7.46  thf('11', plain,
% 7.28/7.46      (![X37 : $i]:
% 7.28/7.46         (~ (r2_hidden @ X37 @ sk_B) | (r2_hidden @ (sk_E @ X37) @ sk_A))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf('12', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         ((r1_tarski @ sk_B @ X0)
% 7.28/7.46          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 7.28/7.46      inference('sup-', [status(thm)], ['10', '11'])).
% 7.28/7.46  thf(zf_stmt_2, axiom,
% 7.28/7.46    (![B:$i,A:$i]:
% 7.28/7.46     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.28/7.46       ( zip_tseitin_0 @ B @ A ) ))).
% 7.28/7.46  thf('13', plain,
% 7.28/7.46      (![X29 : $i, X30 : $i]:
% 7.28/7.46         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.28/7.46  thf('14', plain,
% 7.28/7.46      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 7.28/7.46  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 7.28/7.46  thf(zf_stmt_5, axiom,
% 7.28/7.46    (![A:$i,B:$i,C:$i]:
% 7.28/7.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.28/7.46       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 7.28/7.46         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.28/7.46           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 7.28/7.46             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 7.28/7.46  thf('15', plain,
% 7.28/7.46      (![X34 : $i, X35 : $i, X36 : $i]:
% 7.28/7.46         (~ (zip_tseitin_0 @ X34 @ X35)
% 7.28/7.46          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 7.28/7.46          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.28/7.46  thf('16', plain,
% 7.28/7.46      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.28/7.46        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 7.28/7.46      inference('sup-', [status(thm)], ['14', '15'])).
% 7.28/7.46  thf('17', plain,
% 7.28/7.46      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 7.28/7.46      inference('sup-', [status(thm)], ['13', '16'])).
% 7.28/7.46  thf('18', plain,
% 7.28/7.46      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.28/7.46        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('demod', [status(thm)], ['2', '5'])).
% 7.28/7.46  thf('19', plain,
% 7.28/7.46      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('sup-', [status(thm)], ['17', '18'])).
% 7.28/7.46  thf(d5_funct_1, axiom,
% 7.28/7.46    (![A:$i]:
% 7.28/7.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.28/7.46       ( ![B:$i]:
% 7.28/7.46         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 7.28/7.46           ( ![C:$i]:
% 7.28/7.46             ( ( r2_hidden @ C @ B ) <=>
% 7.28/7.46               ( ?[D:$i]:
% 7.28/7.46                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 7.28/7.46                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 7.28/7.46  thf('20', plain,
% 7.28/7.46      (![X11 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 7.28/7.46         (((X13) != (k2_relat_1 @ X11))
% 7.28/7.46          | (r2_hidden @ X15 @ X13)
% 7.28/7.46          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X11))
% 7.28/7.46          | ((X15) != (k1_funct_1 @ X11 @ X16))
% 7.28/7.46          | ~ (v1_funct_1 @ X11)
% 7.28/7.46          | ~ (v1_relat_1 @ X11))),
% 7.28/7.46      inference('cnf', [status(esa)], [d5_funct_1])).
% 7.28/7.46  thf('21', plain,
% 7.28/7.46      (![X11 : $i, X16 : $i]:
% 7.28/7.46         (~ (v1_relat_1 @ X11)
% 7.28/7.46          | ~ (v1_funct_1 @ X11)
% 7.28/7.46          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X11))
% 7.28/7.46          | (r2_hidden @ (k1_funct_1 @ X11 @ X16) @ (k2_relat_1 @ X11)))),
% 7.28/7.46      inference('simplify', [status(thm)], ['20'])).
% 7.28/7.46  thf('22', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         (~ (r2_hidden @ X0 @ sk_A)
% 7.28/7.46          | ((sk_B) = (k1_xboole_0))
% 7.28/7.46          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 7.28/7.46          | ~ (v1_funct_1 @ sk_C_2)
% 7.28/7.46          | ~ (v1_relat_1 @ sk_C_2))),
% 7.28/7.46      inference('sup-', [status(thm)], ['19', '21'])).
% 7.28/7.46  thf('23', plain, ((v1_funct_1 @ sk_C_2)),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf('24', plain,
% 7.28/7.46      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf(cc1_relset_1, axiom,
% 7.28/7.46    (![A:$i,B:$i,C:$i]:
% 7.28/7.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.28/7.46       ( v1_relat_1 @ C ) ))).
% 7.28/7.46  thf('25', plain,
% 7.28/7.46      (![X17 : $i, X18 : $i, X19 : $i]:
% 7.28/7.46         ((v1_relat_1 @ X17)
% 7.28/7.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 7.28/7.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.28/7.46  thf('26', plain, ((v1_relat_1 @ sk_C_2)),
% 7.28/7.46      inference('sup-', [status(thm)], ['24', '25'])).
% 7.28/7.46  thf('27', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         (~ (r2_hidden @ X0 @ sk_A)
% 7.28/7.46          | ((sk_B) = (k1_xboole_0))
% 7.28/7.46          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('demod', [status(thm)], ['22', '23', '26'])).
% 7.28/7.46  thf('28', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         ((r1_tarski @ sk_B @ X0)
% 7.28/7.46          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 7.28/7.46             (k2_relat_1 @ sk_C_2))
% 7.28/7.46          | ((sk_B) = (k1_xboole_0)))),
% 7.28/7.46      inference('sup-', [status(thm)], ['12', '27'])).
% 7.28/7.46  thf('29', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 7.28/7.46          | (r1_tarski @ sk_B @ X0)
% 7.28/7.46          | ((sk_B) = (k1_xboole_0))
% 7.28/7.46          | (r1_tarski @ sk_B @ X0))),
% 7.28/7.46      inference('sup+', [status(thm)], ['9', '28'])).
% 7.28/7.46  thf('30', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         (((sk_B) = (k1_xboole_0))
% 7.28/7.46          | (r1_tarski @ sk_B @ X0)
% 7.28/7.46          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('simplify', [status(thm)], ['29'])).
% 7.28/7.46  thf('31', plain,
% 7.28/7.46      (![X1 : $i, X3 : $i]:
% 7.28/7.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.28/7.46      inference('cnf', [status(esa)], [d3_tarski])).
% 7.28/7.46  thf('32', plain,
% 7.28/7.46      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 7.28/7.46        | ((sk_B) = (k1_xboole_0))
% 7.28/7.46        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('sup-', [status(thm)], ['30', '31'])).
% 7.28/7.46  thf('33', plain,
% 7.28/7.46      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('simplify', [status(thm)], ['32'])).
% 7.28/7.46  thf(d10_xboole_0, axiom,
% 7.28/7.46    (![A:$i,B:$i]:
% 7.28/7.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.28/7.46  thf('34', plain,
% 7.28/7.46      (![X4 : $i, X6 : $i]:
% 7.28/7.46         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 7.28/7.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.28/7.46  thf('35', plain,
% 7.28/7.46      ((((sk_B) = (k1_xboole_0))
% 7.28/7.46        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)
% 7.28/7.46        | ((k2_relat_1 @ sk_C_2) = (sk_B)))),
% 7.28/7.46      inference('sup-', [status(thm)], ['33', '34'])).
% 7.28/7.46  thf('36', plain,
% 7.28/7.46      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf(cc2_relset_1, axiom,
% 7.28/7.46    (![A:$i,B:$i,C:$i]:
% 7.28/7.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.28/7.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.28/7.46  thf('37', plain,
% 7.28/7.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 7.28/7.46         ((v5_relat_1 @ X20 @ X22)
% 7.28/7.46          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 7.28/7.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.28/7.46  thf('38', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 7.28/7.46      inference('sup-', [status(thm)], ['36', '37'])).
% 7.28/7.46  thf(d19_relat_1, axiom,
% 7.28/7.46    (![A:$i,B:$i]:
% 7.28/7.46     ( ( v1_relat_1 @ B ) =>
% 7.28/7.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 7.28/7.46  thf('39', plain,
% 7.28/7.46      (![X7 : $i, X8 : $i]:
% 7.28/7.46         (~ (v5_relat_1 @ X7 @ X8)
% 7.28/7.46          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 7.28/7.46          | ~ (v1_relat_1 @ X7))),
% 7.28/7.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.28/7.46  thf('40', plain,
% 7.28/7.46      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 7.28/7.46      inference('sup-', [status(thm)], ['38', '39'])).
% 7.28/7.46  thf('41', plain, ((v1_relat_1 @ sk_C_2)),
% 7.28/7.46      inference('sup-', [status(thm)], ['24', '25'])).
% 7.28/7.46  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 7.28/7.46      inference('demod', [status(thm)], ['40', '41'])).
% 7.28/7.46  thf('43', plain,
% 7.28/7.46      ((((sk_B) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C_2) = (sk_B)))),
% 7.28/7.46      inference('demod', [status(thm)], ['35', '42'])).
% 7.28/7.46  thf('44', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf('45', plain,
% 7.28/7.46      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf(redefinition_k2_relset_1, axiom,
% 7.28/7.46    (![A:$i,B:$i,C:$i]:
% 7.28/7.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.28/7.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 7.28/7.46  thf('46', plain,
% 7.28/7.46      (![X26 : $i, X27 : $i, X28 : $i]:
% 7.28/7.46         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 7.28/7.46          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 7.28/7.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 7.28/7.46  thf('47', plain,
% 7.28/7.46      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 7.28/7.46      inference('sup-', [status(thm)], ['45', '46'])).
% 7.28/7.46  thf('48', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 7.28/7.46      inference('demod', [status(thm)], ['44', '47'])).
% 7.28/7.46  thf('49', plain, (((sk_B) = (k1_xboole_0))),
% 7.28/7.46      inference('simplify_reflect-', [status(thm)], ['43', '48'])).
% 7.28/7.46  thf('50', plain,
% 7.28/7.46      ((~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A)
% 7.28/7.46        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('demod', [status(thm)], ['6', '49'])).
% 7.28/7.46  thf('51', plain,
% 7.28/7.46      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf('52', plain, (((sk_B) = (k1_xboole_0))),
% 7.28/7.46      inference('simplify_reflect-', [status(thm)], ['43', '48'])).
% 7.28/7.46  thf('53', plain,
% 7.28/7.46      ((m1_subset_1 @ sk_C_2 @ 
% 7.28/7.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 7.28/7.46      inference('demod', [status(thm)], ['51', '52'])).
% 7.28/7.46  thf('54', plain,
% 7.28/7.46      (![X34 : $i, X35 : $i, X36 : $i]:
% 7.28/7.46         (((X34) != (k1_xboole_0))
% 7.28/7.46          | ((X35) = (k1_xboole_0))
% 7.28/7.46          | ((X36) = (k1_xboole_0))
% 7.28/7.46          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 7.28/7.46          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.28/7.46  thf('55', plain,
% 7.28/7.46      (![X35 : $i, X36 : $i]:
% 7.28/7.46         (~ (m1_subset_1 @ X36 @ 
% 7.28/7.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ k1_xboole_0)))
% 7.28/7.46          | ~ (v1_funct_2 @ X36 @ X35 @ k1_xboole_0)
% 7.28/7.46          | ((X36) = (k1_xboole_0))
% 7.28/7.46          | ((X35) = (k1_xboole_0)))),
% 7.28/7.46      inference('simplify', [status(thm)], ['54'])).
% 7.28/7.46  thf('56', plain,
% 7.28/7.46      ((((sk_A) = (k1_xboole_0))
% 7.28/7.46        | ((sk_C_2) = (k1_xboole_0))
% 7.28/7.46        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0))),
% 7.28/7.46      inference('sup-', [status(thm)], ['53', '55'])).
% 7.28/7.46  thf('57', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.28/7.46  thf('58', plain, (((sk_B) = (k1_xboole_0))),
% 7.28/7.46      inference('simplify_reflect-', [status(thm)], ['43', '48'])).
% 7.28/7.46  thf('59', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0)),
% 7.28/7.46      inference('demod', [status(thm)], ['57', '58'])).
% 7.28/7.46  thf('60', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 7.28/7.46      inference('demod', [status(thm)], ['56', '59'])).
% 7.28/7.46  thf('61', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 7.28/7.46      inference('demod', [status(thm)], ['44', '47'])).
% 7.28/7.46  thf('62', plain, (((sk_B) = (k1_xboole_0))),
% 7.28/7.46      inference('simplify_reflect-', [status(thm)], ['43', '48'])).
% 7.28/7.46  thf('63', plain, (((k2_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 7.28/7.46      inference('demod', [status(thm)], ['61', '62'])).
% 7.28/7.46  thf('64', plain,
% 7.28/7.46      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 7.28/7.46        | ((sk_A) = (k1_xboole_0)))),
% 7.28/7.46      inference('sup-', [status(thm)], ['60', '63'])).
% 7.28/7.46  thf(t60_relat_1, axiom,
% 7.28/7.46    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 7.28/7.46     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 7.28/7.46  thf('65', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 7.28/7.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 7.28/7.46  thf('66', plain,
% 7.28/7.46      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 7.28/7.46      inference('demod', [status(thm)], ['64', '65'])).
% 7.28/7.46  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 7.28/7.46      inference('simplify', [status(thm)], ['66'])).
% 7.28/7.46  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 7.28/7.46      inference('simplify', [status(thm)], ['66'])).
% 7.28/7.46  thf('69', plain,
% 7.28/7.46      ((~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 7.28/7.46        | ((k1_xboole_0) = (k1_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('demod', [status(thm)], ['50', '67', '68'])).
% 7.28/7.46  thf('70', plain,
% 7.28/7.46      ((m1_subset_1 @ sk_C_2 @ 
% 7.28/7.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 7.28/7.46      inference('demod', [status(thm)], ['51', '52'])).
% 7.28/7.46  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 7.28/7.46      inference('simplify', [status(thm)], ['66'])).
% 7.28/7.46  thf('72', plain,
% 7.28/7.46      ((m1_subset_1 @ sk_C_2 @ 
% 7.28/7.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 7.28/7.46      inference('demod', [status(thm)], ['70', '71'])).
% 7.28/7.46  thf('73', plain,
% 7.28/7.46      (![X34 : $i, X35 : $i, X36 : $i]:
% 7.28/7.46         (~ (zip_tseitin_0 @ X34 @ X35)
% 7.28/7.46          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 7.28/7.46          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.28/7.46  thf('74', plain,
% 7.28/7.46      (((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 7.28/7.46        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 7.28/7.46      inference('sup-', [status(thm)], ['72', '73'])).
% 7.28/7.46  thf('75', plain,
% 7.28/7.46      (![X29 : $i, X30 : $i]:
% 7.28/7.46         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.28/7.46  thf('76', plain,
% 7.28/7.46      (![X29 : $i, X30 : $i]:
% 7.28/7.46         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.28/7.46  thf('77', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 7.28/7.46      inference('simplify', [status(thm)], ['76'])).
% 7.28/7.46  thf('78', plain,
% 7.28/7.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.28/7.46         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 7.28/7.46      inference('sup+', [status(thm)], ['75', '77'])).
% 7.28/7.46  thf('79', plain,
% 7.28/7.46      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.28/7.46        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 7.28/7.46      inference('sup-', [status(thm)], ['14', '15'])).
% 7.28/7.46  thf('80', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         ((zip_tseitin_0 @ sk_A @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 7.28/7.46      inference('sup-', [status(thm)], ['78', '79'])).
% 7.28/7.46  thf('81', plain,
% 7.28/7.46      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.28/7.46        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('demod', [status(thm)], ['2', '5'])).
% 7.28/7.46  thf('82', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.28/7.46      inference('sup-', [status(thm)], ['80', '81'])).
% 7.28/7.46  thf(t65_relat_1, axiom,
% 7.28/7.46    (![A:$i]:
% 7.28/7.46     ( ( v1_relat_1 @ A ) =>
% 7.28/7.46       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 7.28/7.46         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 7.28/7.46  thf('83', plain,
% 7.28/7.46      (![X9 : $i]:
% 7.28/7.46         (((k1_relat_1 @ X9) != (k1_xboole_0))
% 7.28/7.46          | ((k2_relat_1 @ X9) = (k1_xboole_0))
% 7.28/7.46          | ~ (v1_relat_1 @ X9))),
% 7.28/7.46      inference('cnf', [status(esa)], [t65_relat_1])).
% 7.28/7.46  thf('84', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         (((sk_A) != (k1_xboole_0))
% 7.28/7.46          | (zip_tseitin_0 @ sk_A @ X0)
% 7.28/7.46          | ~ (v1_relat_1 @ sk_C_2)
% 7.28/7.46          | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 7.28/7.46      inference('sup-', [status(thm)], ['82', '83'])).
% 7.28/7.46  thf('85', plain, ((v1_relat_1 @ sk_C_2)),
% 7.28/7.46      inference('sup-', [status(thm)], ['24', '25'])).
% 7.28/7.46  thf('86', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         (((sk_A) != (k1_xboole_0))
% 7.28/7.46          | (zip_tseitin_0 @ sk_A @ X0)
% 7.28/7.46          | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 7.28/7.46      inference('demod', [status(thm)], ['84', '85'])).
% 7.28/7.46  thf('87', plain,
% 7.28/7.46      (![X29 : $i, X30 : $i]:
% 7.28/7.46         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 7.28/7.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.28/7.46  thf('88', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         (((k2_relat_1 @ sk_C_2) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_A @ X0))),
% 7.28/7.46      inference('clc', [status(thm)], ['86', '87'])).
% 7.28/7.46  thf('89', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 7.28/7.46      inference('demod', [status(thm)], ['44', '47'])).
% 7.28/7.46  thf('90', plain,
% 7.28/7.46      (![X0 : $i]: (((k1_xboole_0) != (sk_B)) | (zip_tseitin_0 @ sk_A @ X0))),
% 7.28/7.46      inference('sup-', [status(thm)], ['88', '89'])).
% 7.28/7.46  thf('91', plain, (((sk_B) = (k1_xboole_0))),
% 7.28/7.46      inference('simplify_reflect-', [status(thm)], ['43', '48'])).
% 7.28/7.46  thf('92', plain,
% 7.28/7.46      (![X0 : $i]:
% 7.28/7.46         (((k1_xboole_0) != (k1_xboole_0)) | (zip_tseitin_0 @ sk_A @ X0))),
% 7.28/7.46      inference('demod', [status(thm)], ['90', '91'])).
% 7.28/7.46  thf('93', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 7.28/7.46      inference('simplify', [status(thm)], ['92'])).
% 7.28/7.46  thf('94', plain, (((sk_A) = (k1_xboole_0))),
% 7.28/7.46      inference('simplify', [status(thm)], ['66'])).
% 7.28/7.46  thf('95', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 7.28/7.46      inference('demod', [status(thm)], ['93', '94'])).
% 7.28/7.46  thf('96', plain, ((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)),
% 7.28/7.46      inference('demod', [status(thm)], ['74', '95'])).
% 7.28/7.46  thf('97', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C_2))),
% 7.28/7.46      inference('demod', [status(thm)], ['69', '96'])).
% 7.28/7.46  thf('98', plain,
% 7.28/7.46      (![X9 : $i]:
% 7.28/7.46         (((k1_relat_1 @ X9) != (k1_xboole_0))
% 7.28/7.46          | ((k2_relat_1 @ X9) = (k1_xboole_0))
% 7.28/7.46          | ~ (v1_relat_1 @ X9))),
% 7.28/7.46      inference('cnf', [status(esa)], [t65_relat_1])).
% 7.28/7.46  thf('99', plain,
% 7.28/7.46      ((((k1_xboole_0) != (k1_xboole_0))
% 7.28/7.46        | ~ (v1_relat_1 @ sk_C_2)
% 7.28/7.46        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 7.28/7.46      inference('sup-', [status(thm)], ['97', '98'])).
% 7.28/7.46  thf('100', plain, ((v1_relat_1 @ sk_C_2)),
% 7.28/7.46      inference('sup-', [status(thm)], ['24', '25'])).
% 7.28/7.46  thf('101', plain,
% 7.28/7.46      ((((k1_xboole_0) != (k1_xboole_0))
% 7.28/7.46        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 7.28/7.46      inference('demod', [status(thm)], ['99', '100'])).
% 7.28/7.46  thf('102', plain, (((k2_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 7.28/7.46      inference('simplify', [status(thm)], ['101'])).
% 7.28/7.46  thf('103', plain, (((k2_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 7.28/7.46      inference('demod', [status(thm)], ['61', '62'])).
% 7.28/7.46  thf('104', plain, ($false),
% 7.28/7.46      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 7.28/7.46  
% 7.28/7.46  % SZS output end Refutation
% 7.28/7.46  
% 7.28/7.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
