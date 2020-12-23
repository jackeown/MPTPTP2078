%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZxdY0jVQHI

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:24 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 162 expanded)
%              Number of leaves         :   38 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  742 (1838 expanded)
%              Number of equality atoms :   46 ( 112 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(simplify,[status(thm)],['12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('18',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_B )
      | ( X39
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X39 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(simplify,[status(thm)],['12'])).

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

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['26','43'])).

thf('45',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('46',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

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

thf('47',plain,(
    ! [X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( X20
       != ( k1_funct_1 @ X16 @ X21 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('48',plain,(
    ! [X16: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X21 ) @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('55',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['49','50','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['25','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['19','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZxdY0jVQHI
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.82  % Solved by: fo/fo7.sh
% 0.61/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.82  % done 234 iterations in 0.366s
% 0.61/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.82  % SZS output start Refutation
% 0.61/0.82  thf(sk_E_type, type, sk_E: $i > $i).
% 0.61/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.82  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.61/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.82  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.61/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.61/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.61/0.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.61/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.82  thf(d3_tarski, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.82  thf('0', plain,
% 0.61/0.82      (![X1 : $i, X3 : $i]:
% 0.61/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf(t16_funct_2, conjecture,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.82       ( ( ![D:$i]:
% 0.61/0.82           ( ~( ( r2_hidden @ D @ B ) & 
% 0.61/0.82                ( ![E:$i]:
% 0.61/0.82                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.61/0.82                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.61/0.82         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.61/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.82        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.82            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.82          ( ( ![D:$i]:
% 0.61/0.82              ( ~( ( r2_hidden @ D @ B ) & 
% 0.61/0.82                   ( ![E:$i]:
% 0.61/0.82                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.61/0.82                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.61/0.82            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.61/0.82    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.61/0.82  thf('1', plain,
% 0.61/0.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(dt_k2_relset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.82       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.61/0.82  thf('2', plain,
% 0.61/0.82      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.61/0.82         ((m1_subset_1 @ (k2_relset_1 @ X22 @ X23 @ X24) @ (k1_zfmisc_1 @ X23))
% 0.61/0.82          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.61/0.82      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.61/0.82  thf('3', plain,
% 0.61/0.82      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 0.61/0.82        (k1_zfmisc_1 @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.82  thf('4', plain,
% 0.61/0.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(redefinition_k2_relset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.82       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.61/0.82  thf('5', plain,
% 0.61/0.82      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.61/0.82         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.61/0.82          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.61/0.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.61/0.82  thf('6', plain,
% 0.61/0.82      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.61/0.82      inference('sup-', [status(thm)], ['4', '5'])).
% 0.61/0.82  thf('7', plain,
% 0.61/0.82      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['3', '6'])).
% 0.61/0.82  thf(l3_subset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.61/0.82  thf('8', plain,
% 0.61/0.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X8 @ X9)
% 0.61/0.82          | (r2_hidden @ X8 @ X10)
% 0.61/0.82          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.61/0.82      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.61/0.82  thf('9', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.61/0.82  thf('10', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 0.61/0.82          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['0', '9'])).
% 0.61/0.82  thf('11', plain,
% 0.61/0.82      (![X1 : $i, X3 : $i]:
% 0.61/0.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf('12', plain,
% 0.61/0.82      (((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)
% 0.61/0.82        | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['10', '11'])).
% 0.61/0.82  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.61/0.82      inference('simplify', [status(thm)], ['12'])).
% 0.61/0.82  thf(d10_xboole_0, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.82  thf('14', plain,
% 0.61/0.82      (![X4 : $i, X6 : $i]:
% 0.61/0.82         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.61/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.82  thf('15', plain,
% 0.61/0.82      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.61/0.82        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['13', '14'])).
% 0.61/0.82  thf('16', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('17', plain,
% 0.61/0.82      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.61/0.82      inference('sup-', [status(thm)], ['4', '5'])).
% 0.61/0.82  thf('18', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['16', '17'])).
% 0.61/0.82  thf('19', plain, (~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.61/0.82      inference('simplify_reflect-', [status(thm)], ['15', '18'])).
% 0.61/0.82  thf('20', plain,
% 0.61/0.82      (![X1 : $i, X3 : $i]:
% 0.61/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf('21', plain,
% 0.61/0.82      (![X39 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X39 @ sk_B)
% 0.61/0.82          | ((X39) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X39))))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('22', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_B @ X0)
% 0.61/0.82          | ((sk_C @ X0 @ sk_B)
% 0.61/0.82              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.61/0.82      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.82  thf('23', plain,
% 0.61/0.82      (![X1 : $i, X3 : $i]:
% 0.61/0.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf('24', plain,
% 0.61/0.82      (![X39 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X39 @ sk_B) | (r2_hidden @ (sk_E @ X39) @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('25', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_B @ X0)
% 0.61/0.82          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['23', '24'])).
% 0.61/0.82  thf('26', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.61/0.82      inference('simplify', [status(thm)], ['12'])).
% 0.61/0.82  thf(d1_funct_2, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.61/0.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.61/0.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.61/0.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.61/0.82  thf(zf_stmt_1, axiom,
% 0.61/0.82    (![B:$i,A:$i]:
% 0.61/0.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.82       ( zip_tseitin_0 @ B @ A ) ))).
% 0.61/0.82  thf('27', plain,
% 0.61/0.82      (![X31 : $i, X32 : $i]:
% 0.61/0.82         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.82  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.61/0.82  thf('28', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.61/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.61/0.82  thf('29', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.82         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.61/0.82      inference('sup+', [status(thm)], ['27', '28'])).
% 0.61/0.82  thf('30', plain,
% 0.61/0.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.61/0.82  thf(zf_stmt_3, axiom,
% 0.61/0.82    (![C:$i,B:$i,A:$i]:
% 0.61/0.82     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.61/0.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.61/0.82  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.61/0.82  thf(zf_stmt_5, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.82       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.61/0.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.61/0.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.61/0.82  thf('31', plain,
% 0.61/0.82      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.61/0.82         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.61/0.82          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.61/0.82          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.61/0.82  thf('32', plain,
% 0.61/0.82      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.61/0.82        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['30', '31'])).
% 0.61/0.82  thf('33', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['29', '32'])).
% 0.61/0.82  thf('34', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('35', plain,
% 0.61/0.82      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.61/0.82         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.61/0.82          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.61/0.82          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.82  thf('36', plain,
% 0.61/0.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.61/0.82        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.82  thf('37', plain,
% 0.61/0.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.82       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.82  thf('38', plain,
% 0.61/0.82      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.61/0.82         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.61/0.82          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.61/0.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.82  thf('39', plain,
% 0.61/0.82      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.61/0.82      inference('sup-', [status(thm)], ['37', '38'])).
% 0.61/0.82  thf('40', plain,
% 0.61/0.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.61/0.82        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.61/0.82      inference('demod', [status(thm)], ['36', '39'])).
% 0.61/0.82  thf('41', plain,
% 0.61/0.82      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['33', '40'])).
% 0.61/0.82  thf('42', plain,
% 0.61/0.82      (![X4 : $i, X6 : $i]:
% 0.61/0.82         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.61/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.82  thf('43', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 0.61/0.82          | ~ (r1_tarski @ X0 @ sk_B)
% 0.61/0.82          | ((X0) = (sk_B)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['41', '42'])).
% 0.61/0.82  thf('44', plain,
% 0.61/0.82      ((((k2_relat_1 @ sk_C_2) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['26', '43'])).
% 0.61/0.82  thf('45', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['16', '17'])).
% 0.61/0.82  thf('46', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.61/0.82      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.61/0.82  thf(d5_funct_1, axiom,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.82       ( ![B:$i]:
% 0.61/0.82         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.61/0.82           ( ![C:$i]:
% 0.61/0.82             ( ( r2_hidden @ C @ B ) <=>
% 0.61/0.82               ( ?[D:$i]:
% 0.61/0.82                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.61/0.82                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.61/0.82  thf('47', plain,
% 0.61/0.82      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.61/0.82         (((X18) != (k2_relat_1 @ X16))
% 0.61/0.82          | (r2_hidden @ X20 @ X18)
% 0.61/0.82          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.61/0.82          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 0.61/0.82          | ~ (v1_funct_1 @ X16)
% 0.61/0.82          | ~ (v1_relat_1 @ X16))),
% 0.61/0.82      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.61/0.82  thf('48', plain,
% 0.61/0.82      (![X16 : $i, X21 : $i]:
% 0.61/0.82         (~ (v1_relat_1 @ X16)
% 0.61/0.82          | ~ (v1_funct_1 @ X16)
% 0.61/0.82          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.61/0.82          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 0.61/0.82      inference('simplify', [status(thm)], ['47'])).
% 0.61/0.82  thf('49', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.82          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.61/0.82          | ~ (v1_funct_1 @ sk_C_2)
% 0.61/0.82          | ~ (v1_relat_1 @ sk_C_2))),
% 0.61/0.82      inference('sup-', [status(thm)], ['46', '48'])).
% 0.61/0.82  thf('50', plain, ((v1_funct_1 @ sk_C_2)),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf('51', plain,
% 0.61/0.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(cc2_relat_1, axiom,
% 0.61/0.82    (![A:$i]:
% 0.61/0.82     ( ( v1_relat_1 @ A ) =>
% 0.61/0.82       ( ![B:$i]:
% 0.61/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.61/0.82  thf('52', plain,
% 0.61/0.82      (![X11 : $i, X12 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.61/0.82          | (v1_relat_1 @ X11)
% 0.61/0.82          | ~ (v1_relat_1 @ X12))),
% 0.61/0.82      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.61/0.82  thf('53', plain,
% 0.61/0.82      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.61/0.82      inference('sup-', [status(thm)], ['51', '52'])).
% 0.61/0.82  thf(fc6_relat_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.61/0.82  thf('54', plain,
% 0.61/0.82      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.61/0.82      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.61/0.82  thf('55', plain, ((v1_relat_1 @ sk_C_2)),
% 0.61/0.82      inference('demod', [status(thm)], ['53', '54'])).
% 0.61/0.82  thf('56', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.82          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.82      inference('demod', [status(thm)], ['49', '50', '55'])).
% 0.61/0.82  thf('57', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_B @ X0)
% 0.61/0.82          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.61/0.82             (k2_relat_1 @ sk_C_2)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['25', '56'])).
% 0.61/0.82  thf('58', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 0.61/0.82          | (r1_tarski @ sk_B @ X0)
% 0.61/0.82          | (r1_tarski @ sk_B @ X0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['22', '57'])).
% 0.61/0.82  thf('59', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((r1_tarski @ sk_B @ X0)
% 0.61/0.82          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.82      inference('simplify', [status(thm)], ['58'])).
% 0.61/0.82  thf('60', plain,
% 0.61/0.82      (![X1 : $i, X3 : $i]:
% 0.61/0.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.61/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.82  thf('61', plain,
% 0.61/0.82      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.61/0.82        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['59', '60'])).
% 0.61/0.82  thf('62', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.61/0.82      inference('simplify', [status(thm)], ['61'])).
% 0.61/0.82  thf('63', plain, ($false), inference('demod', [status(thm)], ['19', '62'])).
% 0.61/0.82  
% 0.61/0.82  % SZS output end Refutation
% 0.61/0.82  
% 0.61/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
