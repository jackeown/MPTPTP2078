%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0PWqF2QF3T

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:25 EST 2020

% Result     : Theorem 31.85s
% Output     : Refutation 31.85s
% Verified   : 
% Statistics : Number of formulae       :  149 (2043 expanded)
%              Number of leaves         :   38 ( 599 expanded)
%              Depth                    :   31
%              Number of atoms          : 1053 (28238 expanded)
%              Number of equality atoms :   88 (1955 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X38: $i] :
      ( ~ ( r2_hidden @ X38 @ sk_B )
      | ( X38
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X38 ) ) ) ) ),
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
    ! [X38: $i] :
      ( ~ ( r2_hidden @ X38 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X38 ) @ sk_A ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X15: $i,X17: $i,X19: $i,X20: $i] :
      ( ( X17
       != ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ X19 @ X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X15 ) )
      | ( X19
       != ( k1_funct_1 @ X15 @ X20 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('35',plain,(
    ! [X15: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X20 ) @ ( k2_relat_1 @ X15 ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['36','37','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','13'])).

thf('51',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['14','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('54',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('55',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('56',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ k1_xboole_0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('59',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('60',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35 != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('70',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('73',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('74',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('76',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','78'])).

thf('80',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('81',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('82',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('85',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('88',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('92',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('93',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['94'])).

thf('96',plain,(
    zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['90','95'])).

thf('97',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['85','96'])).

thf('98',plain,(
    ! [X15: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X20 ) @ ( k2_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['40','41'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ k1_xboole_0 ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['79','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('107',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['52','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0PWqF2QF3T
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 31.85/32.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 31.85/32.05  % Solved by: fo/fo7.sh
% 31.85/32.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.85/32.05  % done 7603 iterations in 31.589s
% 31.85/32.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 31.85/32.05  % SZS output start Refutation
% 31.85/32.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 31.85/32.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 31.85/32.05  thf(sk_E_type, type, sk_E: $i > $i).
% 31.85/32.05  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 31.85/32.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 31.85/32.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 31.85/32.05  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 31.85/32.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 31.85/32.05  thf(sk_A_type, type, sk_A: $i).
% 31.85/32.05  thf(sk_B_type, type, sk_B: $i).
% 31.85/32.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 31.85/32.05  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 31.85/32.05  thf(sk_C_2_type, type, sk_C_2: $i).
% 31.85/32.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 31.85/32.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 31.85/32.05  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 31.85/32.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 31.85/32.05  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 31.85/32.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 31.85/32.05  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 31.85/32.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 31.85/32.05  thf(t16_funct_2, conjecture,
% 31.85/32.05    (![A:$i,B:$i,C:$i]:
% 31.85/32.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 31.85/32.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 31.85/32.05       ( ( ![D:$i]:
% 31.85/32.05           ( ~( ( r2_hidden @ D @ B ) & 
% 31.85/32.05                ( ![E:$i]:
% 31.85/32.05                  ( ~( ( r2_hidden @ E @ A ) & 
% 31.85/32.05                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 31.85/32.05         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 31.85/32.05  thf(zf_stmt_0, negated_conjecture,
% 31.85/32.05    (~( ![A:$i,B:$i,C:$i]:
% 31.85/32.05        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 31.85/32.05            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 31.85/32.05          ( ( ![D:$i]:
% 31.85/32.05              ( ~( ( r2_hidden @ D @ B ) & 
% 31.85/32.05                   ( ![E:$i]:
% 31.85/32.05                     ( ~( ( r2_hidden @ E @ A ) & 
% 31.85/32.05                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 31.85/32.05            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 31.85/32.05    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 31.85/32.05  thf('0', plain,
% 31.85/32.05      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf(dt_k2_relset_1, axiom,
% 31.85/32.05    (![A:$i,B:$i,C:$i]:
% 31.85/32.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.85/32.05       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 31.85/32.05  thf('1', plain,
% 31.85/32.05      (![X21 : $i, X22 : $i, X23 : $i]:
% 31.85/32.05         ((m1_subset_1 @ (k2_relset_1 @ X21 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 31.85/32.05          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 31.85/32.05      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 31.85/32.05  thf('2', plain,
% 31.85/32.05      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 31.85/32.05        (k1_zfmisc_1 @ sk_B))),
% 31.85/32.05      inference('sup-', [status(thm)], ['0', '1'])).
% 31.85/32.05  thf('3', plain,
% 31.85/32.05      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf(redefinition_k2_relset_1, axiom,
% 31.85/32.05    (![A:$i,B:$i,C:$i]:
% 31.85/32.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.85/32.05       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 31.85/32.05  thf('4', plain,
% 31.85/32.05      (![X27 : $i, X28 : $i, X29 : $i]:
% 31.85/32.05         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 31.85/32.05          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 31.85/32.05      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 31.85/32.05  thf('5', plain,
% 31.85/32.05      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('sup-', [status(thm)], ['3', '4'])).
% 31.85/32.05  thf('6', plain,
% 31.85/32.05      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 31.85/32.05      inference('demod', [status(thm)], ['2', '5'])).
% 31.85/32.05  thf(t3_subset, axiom,
% 31.85/32.05    (![A:$i,B:$i]:
% 31.85/32.05     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 31.85/32.05  thf('7', plain,
% 31.85/32.05      (![X7 : $i, X8 : $i]:
% 31.85/32.05         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 31.85/32.05      inference('cnf', [status(esa)], [t3_subset])).
% 31.85/32.05  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 31.85/32.05      inference('sup-', [status(thm)], ['6', '7'])).
% 31.85/32.05  thf(d10_xboole_0, axiom,
% 31.85/32.05    (![A:$i,B:$i]:
% 31.85/32.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 31.85/32.05  thf('9', plain,
% 31.85/32.05      (![X4 : $i, X6 : $i]:
% 31.85/32.05         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 31.85/32.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 31.85/32.05  thf('10', plain,
% 31.85/32.05      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 31.85/32.05        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('sup-', [status(thm)], ['8', '9'])).
% 31.85/32.05  thf('11', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf('12', plain,
% 31.85/32.05      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('sup-', [status(thm)], ['3', '4'])).
% 31.85/32.05  thf('13', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 31.85/32.05      inference('demod', [status(thm)], ['11', '12'])).
% 31.85/32.05  thf('14', plain, (~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 31.85/32.05  thf(d3_tarski, axiom,
% 31.85/32.05    (![A:$i,B:$i]:
% 31.85/32.05     ( ( r1_tarski @ A @ B ) <=>
% 31.85/32.05       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 31.85/32.05  thf('15', plain,
% 31.85/32.05      (![X1 : $i, X3 : $i]:
% 31.85/32.05         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 31.85/32.05      inference('cnf', [status(esa)], [d3_tarski])).
% 31.85/32.05  thf('16', plain,
% 31.85/32.05      (![X38 : $i]:
% 31.85/32.05         (~ (r2_hidden @ X38 @ sk_B)
% 31.85/32.05          | ((X38) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X38))))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf('17', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r1_tarski @ sk_B @ X0)
% 31.85/32.05          | ((sk_C @ X0 @ sk_B)
% 31.85/32.05              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 31.85/32.05      inference('sup-', [status(thm)], ['15', '16'])).
% 31.85/32.05  thf('18', plain,
% 31.85/32.05      (![X1 : $i, X3 : $i]:
% 31.85/32.05         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 31.85/32.05      inference('cnf', [status(esa)], [d3_tarski])).
% 31.85/32.05  thf('19', plain,
% 31.85/32.05      (![X38 : $i]:
% 31.85/32.05         (~ (r2_hidden @ X38 @ sk_B) | (r2_hidden @ (sk_E @ X38) @ sk_A))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf('20', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r1_tarski @ sk_B @ X0)
% 31.85/32.05          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 31.85/32.05      inference('sup-', [status(thm)], ['18', '19'])).
% 31.85/32.05  thf(d1_funct_2, axiom,
% 31.85/32.05    (![A:$i,B:$i,C:$i]:
% 31.85/32.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.85/32.05       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 31.85/32.05           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 31.85/32.05             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 31.85/32.05         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 31.85/32.05           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 31.85/32.05             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 31.85/32.05  thf(zf_stmt_1, axiom,
% 31.85/32.05    (![B:$i,A:$i]:
% 31.85/32.05     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 31.85/32.05       ( zip_tseitin_0 @ B @ A ) ))).
% 31.85/32.05  thf('21', plain,
% 31.85/32.05      (![X30 : $i, X31 : $i]:
% 31.85/32.05         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 31.85/32.05  thf('22', plain,
% 31.85/32.05      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 31.85/32.05  thf(zf_stmt_3, axiom,
% 31.85/32.05    (![C:$i,B:$i,A:$i]:
% 31.85/32.05     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 31.85/32.05       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 31.85/32.05  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 31.85/32.05  thf(zf_stmt_5, axiom,
% 31.85/32.05    (![A:$i,B:$i,C:$i]:
% 31.85/32.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.85/32.05       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 31.85/32.05         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 31.85/32.05           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 31.85/32.05             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 31.85/32.05  thf('23', plain,
% 31.85/32.05      (![X35 : $i, X36 : $i, X37 : $i]:
% 31.85/32.05         (~ (zip_tseitin_0 @ X35 @ X36)
% 31.85/32.05          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 31.85/32.05          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 31.85/32.05  thf('24', plain,
% 31.85/32.05      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 31.85/32.05        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 31.85/32.05      inference('sup-', [status(thm)], ['22', '23'])).
% 31.85/32.05  thf('25', plain,
% 31.85/32.05      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 31.85/32.05      inference('sup-', [status(thm)], ['21', '24'])).
% 31.85/32.05  thf('26', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf('27', plain,
% 31.85/32.05      (![X32 : $i, X33 : $i, X34 : $i]:
% 31.85/32.05         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 31.85/32.05          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 31.85/32.05          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_3])).
% 31.85/32.05  thf('28', plain,
% 31.85/32.05      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 31.85/32.05        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 31.85/32.05      inference('sup-', [status(thm)], ['26', '27'])).
% 31.85/32.05  thf('29', plain,
% 31.85/32.05      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf(redefinition_k1_relset_1, axiom,
% 31.85/32.05    (![A:$i,B:$i,C:$i]:
% 31.85/32.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 31.85/32.05       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 31.85/32.05  thf('30', plain,
% 31.85/32.05      (![X24 : $i, X25 : $i, X26 : $i]:
% 31.85/32.05         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 31.85/32.05          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 31.85/32.05      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 31.85/32.05  thf('31', plain,
% 31.85/32.05      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('sup-', [status(thm)], ['29', '30'])).
% 31.85/32.05  thf('32', plain,
% 31.85/32.05      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 31.85/32.05        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('demod', [status(thm)], ['28', '31'])).
% 31.85/32.05  thf('33', plain,
% 31.85/32.05      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('sup-', [status(thm)], ['25', '32'])).
% 31.85/32.05  thf(d5_funct_1, axiom,
% 31.85/32.05    (![A:$i]:
% 31.85/32.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 31.85/32.05       ( ![B:$i]:
% 31.85/32.05         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 31.85/32.05           ( ![C:$i]:
% 31.85/32.05             ( ( r2_hidden @ C @ B ) <=>
% 31.85/32.05               ( ?[D:$i]:
% 31.85/32.05                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 31.85/32.05                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 31.85/32.05  thf('34', plain,
% 31.85/32.05      (![X15 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 31.85/32.05         (((X17) != (k2_relat_1 @ X15))
% 31.85/32.05          | (r2_hidden @ X19 @ X17)
% 31.85/32.05          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X15))
% 31.85/32.05          | ((X19) != (k1_funct_1 @ X15 @ X20))
% 31.85/32.05          | ~ (v1_funct_1 @ X15)
% 31.85/32.05          | ~ (v1_relat_1 @ X15))),
% 31.85/32.05      inference('cnf', [status(esa)], [d5_funct_1])).
% 31.85/32.05  thf('35', plain,
% 31.85/32.05      (![X15 : $i, X20 : $i]:
% 31.85/32.05         (~ (v1_relat_1 @ X15)
% 31.85/32.05          | ~ (v1_funct_1 @ X15)
% 31.85/32.05          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X15))
% 31.85/32.05          | (r2_hidden @ (k1_funct_1 @ X15 @ X20) @ (k2_relat_1 @ X15)))),
% 31.85/32.05      inference('simplify', [status(thm)], ['34'])).
% 31.85/32.05  thf('36', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         (~ (r2_hidden @ X0 @ sk_A)
% 31.85/32.05          | ((sk_B) = (k1_xboole_0))
% 31.85/32.05          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 31.85/32.05          | ~ (v1_funct_1 @ sk_C_2)
% 31.85/32.05          | ~ (v1_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('sup-', [status(thm)], ['33', '35'])).
% 31.85/32.05  thf('37', plain, ((v1_funct_1 @ sk_C_2)),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf('38', plain,
% 31.85/32.05      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf(cc2_relat_1, axiom,
% 31.85/32.05    (![A:$i]:
% 31.85/32.05     ( ( v1_relat_1 @ A ) =>
% 31.85/32.05       ( ![B:$i]:
% 31.85/32.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 31.85/32.05  thf('39', plain,
% 31.85/32.05      (![X10 : $i, X11 : $i]:
% 31.85/32.05         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 31.85/32.05          | (v1_relat_1 @ X10)
% 31.85/32.05          | ~ (v1_relat_1 @ X11))),
% 31.85/32.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 31.85/32.05  thf('40', plain,
% 31.85/32.05      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('sup-', [status(thm)], ['38', '39'])).
% 31.85/32.05  thf(fc6_relat_1, axiom,
% 31.85/32.05    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 31.85/32.05  thf('41', plain,
% 31.85/32.05      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 31.85/32.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 31.85/32.05  thf('42', plain, ((v1_relat_1 @ sk_C_2)),
% 31.85/32.05      inference('demod', [status(thm)], ['40', '41'])).
% 31.85/32.05  thf('43', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         (~ (r2_hidden @ X0 @ sk_A)
% 31.85/32.05          | ((sk_B) = (k1_xboole_0))
% 31.85/32.05          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('demod', [status(thm)], ['36', '37', '42'])).
% 31.85/32.05  thf('44', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r1_tarski @ sk_B @ X0)
% 31.85/32.05          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 31.85/32.05             (k2_relat_1 @ sk_C_2))
% 31.85/32.05          | ((sk_B) = (k1_xboole_0)))),
% 31.85/32.05      inference('sup-', [status(thm)], ['20', '43'])).
% 31.85/32.05  thf('45', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 31.85/32.05          | (r1_tarski @ sk_B @ X0)
% 31.85/32.05          | ((sk_B) = (k1_xboole_0))
% 31.85/32.05          | (r1_tarski @ sk_B @ X0))),
% 31.85/32.05      inference('sup+', [status(thm)], ['17', '44'])).
% 31.85/32.05  thf('46', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         (((sk_B) = (k1_xboole_0))
% 31.85/32.05          | (r1_tarski @ sk_B @ X0)
% 31.85/32.05          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('simplify', [status(thm)], ['45'])).
% 31.85/32.05  thf('47', plain,
% 31.85/32.05      (![X1 : $i, X3 : $i]:
% 31.85/32.05         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 31.85/32.05      inference('cnf', [status(esa)], [d3_tarski])).
% 31.85/32.05  thf('48', plain,
% 31.85/32.05      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 31.85/32.05        | ((sk_B) = (k1_xboole_0))
% 31.85/32.05        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('sup-', [status(thm)], ['46', '47'])).
% 31.85/32.05  thf('49', plain,
% 31.85/32.05      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('simplify', [status(thm)], ['48'])).
% 31.85/32.05  thf('50', plain, (~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 31.85/32.05  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 31.85/32.05      inference('clc', [status(thm)], ['49', '50'])).
% 31.85/32.05  thf('52', plain, (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('demod', [status(thm)], ['14', '51'])).
% 31.85/32.05  thf('53', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r1_tarski @ sk_B @ X0)
% 31.85/32.05          | ((sk_C @ X0 @ sk_B)
% 31.85/32.05              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 31.85/32.05      inference('sup-', [status(thm)], ['15', '16'])).
% 31.85/32.05  thf('54', plain, (((sk_B) = (k1_xboole_0))),
% 31.85/32.05      inference('clc', [status(thm)], ['49', '50'])).
% 31.85/32.05  thf('55', plain, (((sk_B) = (k1_xboole_0))),
% 31.85/32.05      inference('clc', [status(thm)], ['49', '50'])).
% 31.85/32.05  thf('56', plain, (((sk_B) = (k1_xboole_0))),
% 31.85/32.05      inference('clc', [status(thm)], ['49', '50'])).
% 31.85/32.05  thf('57', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r1_tarski @ k1_xboole_0 @ X0)
% 31.85/32.05          | ((sk_C @ X0 @ k1_xboole_0)
% 31.85/32.05              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ k1_xboole_0)))))),
% 31.85/32.05      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 31.85/32.05  thf('58', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r1_tarski @ sk_B @ X0)
% 31.85/32.05          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 31.85/32.05      inference('sup-', [status(thm)], ['18', '19'])).
% 31.85/32.05  thf('59', plain, (((sk_B) = (k1_xboole_0))),
% 31.85/32.05      inference('clc', [status(thm)], ['49', '50'])).
% 31.85/32.05  thf('60', plain, (((sk_B) = (k1_xboole_0))),
% 31.85/32.05      inference('clc', [status(thm)], ['49', '50'])).
% 31.85/32.05  thf('61', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r1_tarski @ k1_xboole_0 @ X0)
% 31.85/32.05          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ k1_xboole_0)) @ sk_A))),
% 31.85/32.05      inference('demod', [status(thm)], ['58', '59', '60'])).
% 31.85/32.05  thf('62', plain,
% 31.85/32.05      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf('63', plain, (((sk_B) = (k1_xboole_0))),
% 31.85/32.05      inference('clc', [status(thm)], ['49', '50'])).
% 31.85/32.05  thf('64', plain,
% 31.85/32.05      ((m1_subset_1 @ sk_C_2 @ 
% 31.85/32.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 31.85/32.05      inference('demod', [status(thm)], ['62', '63'])).
% 31.85/32.05  thf('65', plain,
% 31.85/32.05      (![X35 : $i, X36 : $i, X37 : $i]:
% 31.85/32.05         (((X35) != (k1_xboole_0))
% 31.85/32.05          | ((X36) = (k1_xboole_0))
% 31.85/32.05          | ((X37) = (k1_xboole_0))
% 31.85/32.05          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 31.85/32.05          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 31.85/32.05  thf('66', plain,
% 31.85/32.05      (![X36 : $i, X37 : $i]:
% 31.85/32.05         (~ (m1_subset_1 @ X37 @ 
% 31.85/32.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ k1_xboole_0)))
% 31.85/32.05          | ~ (v1_funct_2 @ X37 @ X36 @ k1_xboole_0)
% 31.85/32.05          | ((X37) = (k1_xboole_0))
% 31.85/32.05          | ((X36) = (k1_xboole_0)))),
% 31.85/32.05      inference('simplify', [status(thm)], ['65'])).
% 31.85/32.05  thf('67', plain,
% 31.85/32.05      ((((sk_A) = (k1_xboole_0))
% 31.85/32.05        | ((sk_C_2) = (k1_xboole_0))
% 31.85/32.05        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0))),
% 31.85/32.05      inference('sup-', [status(thm)], ['64', '66'])).
% 31.85/32.05  thf('68', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf('69', plain, (((sk_B) = (k1_xboole_0))),
% 31.85/32.05      inference('clc', [status(thm)], ['49', '50'])).
% 31.85/32.05  thf('70', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ k1_xboole_0)),
% 31.85/32.05      inference('demod', [status(thm)], ['68', '69'])).
% 31.85/32.05  thf('71', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 31.85/32.05      inference('demod', [status(thm)], ['67', '70'])).
% 31.85/32.05  thf('72', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 31.85/32.05      inference('demod', [status(thm)], ['11', '12'])).
% 31.85/32.05  thf('73', plain, (((sk_B) = (k1_xboole_0))),
% 31.85/32.05      inference('clc', [status(thm)], ['49', '50'])).
% 31.85/32.05  thf('74', plain, (((k2_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 31.85/32.05      inference('demod', [status(thm)], ['72', '73'])).
% 31.85/32.05  thf('75', plain,
% 31.85/32.05      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 31.85/32.05        | ((sk_A) = (k1_xboole_0)))),
% 31.85/32.05      inference('sup-', [status(thm)], ['71', '74'])).
% 31.85/32.05  thf(t60_relat_1, axiom,
% 31.85/32.05    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 31.85/32.05     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 31.85/32.05  thf('76', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 31.85/32.05      inference('cnf', [status(esa)], [t60_relat_1])).
% 31.85/32.05  thf('77', plain,
% 31.85/32.05      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 31.85/32.05      inference('demod', [status(thm)], ['75', '76'])).
% 31.85/32.05  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 31.85/32.05      inference('simplify', [status(thm)], ['77'])).
% 31.85/32.05  thf('79', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r1_tarski @ k1_xboole_0 @ X0)
% 31.85/32.05          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ k1_xboole_0)) @ k1_xboole_0))),
% 31.85/32.05      inference('demod', [status(thm)], ['61', '78'])).
% 31.85/32.05  thf('80', plain,
% 31.85/32.05      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 31.85/32.05        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('demod', [status(thm)], ['28', '31'])).
% 31.85/32.05  thf('81', plain, (((sk_B) = (k1_xboole_0))),
% 31.85/32.05      inference('clc', [status(thm)], ['49', '50'])).
% 31.85/32.05  thf('82', plain,
% 31.85/32.05      ((~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ sk_A)
% 31.85/32.05        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('demod', [status(thm)], ['80', '81'])).
% 31.85/32.05  thf('83', plain, (((sk_A) = (k1_xboole_0))),
% 31.85/32.05      inference('simplify', [status(thm)], ['77'])).
% 31.85/32.05  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 31.85/32.05      inference('simplify', [status(thm)], ['77'])).
% 31.85/32.05  thf('85', plain,
% 31.85/32.05      ((~ (zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 31.85/32.05        | ((k1_xboole_0) = (k1_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('demod', [status(thm)], ['82', '83', '84'])).
% 31.85/32.05  thf('86', plain,
% 31.85/32.05      ((m1_subset_1 @ sk_C_2 @ 
% 31.85/32.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 31.85/32.05      inference('demod', [status(thm)], ['62', '63'])).
% 31.85/32.05  thf('87', plain, (((sk_A) = (k1_xboole_0))),
% 31.85/32.05      inference('simplify', [status(thm)], ['77'])).
% 31.85/32.05  thf('88', plain,
% 31.85/32.05      ((m1_subset_1 @ sk_C_2 @ 
% 31.85/32.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 31.85/32.05      inference('demod', [status(thm)], ['86', '87'])).
% 31.85/32.05  thf('89', plain,
% 31.85/32.05      (![X35 : $i, X36 : $i, X37 : $i]:
% 31.85/32.05         (~ (zip_tseitin_0 @ X35 @ X36)
% 31.85/32.05          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 31.85/32.05          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 31.85/32.05  thf('90', plain,
% 31.85/32.05      (((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)
% 31.85/32.05        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 31.85/32.05      inference('sup-', [status(thm)], ['88', '89'])).
% 31.85/32.05  thf('91', plain,
% 31.85/32.05      (![X30 : $i, X31 : $i]:
% 31.85/32.05         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 31.85/32.05  thf('92', plain,
% 31.85/32.05      (![X30 : $i, X31 : $i]:
% 31.85/32.05         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 31.85/32.05  thf('93', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 31.85/32.05      inference('simplify', [status(thm)], ['92'])).
% 31.85/32.05  thf('94', plain,
% 31.85/32.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.85/32.05         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 31.85/32.05      inference('sup+', [status(thm)], ['91', '93'])).
% 31.85/32.05  thf('95', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 31.85/32.05      inference('eq_fact', [status(thm)], ['94'])).
% 31.85/32.05  thf('96', plain, ((zip_tseitin_1 @ sk_C_2 @ k1_xboole_0 @ k1_xboole_0)),
% 31.85/32.05      inference('demod', [status(thm)], ['90', '95'])).
% 31.85/32.05  thf('97', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('demod', [status(thm)], ['85', '96'])).
% 31.85/32.05  thf('98', plain,
% 31.85/32.05      (![X15 : $i, X20 : $i]:
% 31.85/32.05         (~ (v1_relat_1 @ X15)
% 31.85/32.05          | ~ (v1_funct_1 @ X15)
% 31.85/32.05          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X15))
% 31.85/32.05          | (r2_hidden @ (k1_funct_1 @ X15 @ X20) @ (k2_relat_1 @ X15)))),
% 31.85/32.05      inference('simplify', [status(thm)], ['34'])).
% 31.85/32.05  thf('99', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 31.85/32.05          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 31.85/32.05          | ~ (v1_funct_1 @ sk_C_2)
% 31.85/32.05          | ~ (v1_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('sup-', [status(thm)], ['97', '98'])).
% 31.85/32.05  thf('100', plain, ((v1_funct_1 @ sk_C_2)),
% 31.85/32.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.85/32.05  thf('101', plain, ((v1_relat_1 @ sk_C_2)),
% 31.85/32.05      inference('demod', [status(thm)], ['40', '41'])).
% 31.85/32.05  thf('102', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 31.85/32.05          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('demod', [status(thm)], ['99', '100', '101'])).
% 31.85/32.05  thf('103', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r1_tarski @ k1_xboole_0 @ X0)
% 31.85/32.05          | (r2_hidden @ 
% 31.85/32.05             (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ k1_xboole_0))) @ 
% 31.85/32.05             (k2_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('sup-', [status(thm)], ['79', '102'])).
% 31.85/32.05  thf('104', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k2_relat_1 @ sk_C_2))
% 31.85/32.05          | (r1_tarski @ k1_xboole_0 @ X0)
% 31.85/32.05          | (r1_tarski @ k1_xboole_0 @ X0))),
% 31.85/32.05      inference('sup+', [status(thm)], ['57', '103'])).
% 31.85/32.05  thf('105', plain,
% 31.85/32.05      (![X0 : $i]:
% 31.85/32.05         ((r1_tarski @ k1_xboole_0 @ X0)
% 31.85/32.05          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k2_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('simplify', [status(thm)], ['104'])).
% 31.85/32.05  thf('106', plain,
% 31.85/32.05      (![X1 : $i, X3 : $i]:
% 31.85/32.05         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 31.85/32.05      inference('cnf', [status(esa)], [d3_tarski])).
% 31.85/32.05  thf('107', plain,
% 31.85/32.05      (((r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_C_2))
% 31.85/32.05        | (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_C_2)))),
% 31.85/32.05      inference('sup-', [status(thm)], ['105', '106'])).
% 31.85/32.05  thf('108', plain, ((r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_C_2))),
% 31.85/32.05      inference('simplify', [status(thm)], ['107'])).
% 31.85/32.05  thf('109', plain, ($false), inference('demod', [status(thm)], ['52', '108'])).
% 31.85/32.05  
% 31.85/32.05  % SZS output end Refutation
% 31.85/32.05  
% 31.85/32.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
