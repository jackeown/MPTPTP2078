%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ckRYcOSFwG

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:19 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 159 expanded)
%              Number of leaves         :   37 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  728 (1824 expanded)
%              Number of equality atoms :   46 ( 112 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X38: $i] :
      ( ~ ( r2_hidden @ X38 @ sk_B )
      | ( X38
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X38 ) ) ) ) ),
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
    ! [X38: $i] :
      ( ~ ( r2_hidden @ X38 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X38 ) @ sk_A ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X12: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( X16
       != ( k1_funct_1 @ X12 @ X17 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('48',plain,(
    ! [X12: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X17 ) @ ( k2_relat_1 @ X12 ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('53',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['49','50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['25','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['19','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ckRYcOSFwG
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:28:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.60/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.87  % Solved by: fo/fo7.sh
% 0.60/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.87  % done 233 iterations in 0.421s
% 0.60/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.87  % SZS output start Refutation
% 0.60/0.87  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.87  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.60/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.60/0.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.87  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.87  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.60/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.87  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.60/0.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.87  thf(sk_E_type, type, sk_E: $i > $i).
% 0.60/0.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.87  thf(d3_tarski, axiom,
% 0.60/0.87    (![A:$i,B:$i]:
% 0.60/0.87     ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.87       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.87  thf('0', plain,
% 0.60/0.87      (![X1 : $i, X3 : $i]:
% 0.60/0.87         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.60/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.87  thf(t16_funct_2, conjecture,
% 0.60/0.87    (![A:$i,B:$i,C:$i]:
% 0.60/0.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.87       ( ( ![D:$i]:
% 0.60/0.87           ( ~( ( r2_hidden @ D @ B ) & 
% 0.60/0.87                ( ![E:$i]:
% 0.60/0.87                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.60/0.87                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.60/0.87         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.60/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.87    (~( ![A:$i,B:$i,C:$i]:
% 0.60/0.87        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.87            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.87          ( ( ![D:$i]:
% 0.60/0.87              ( ~( ( r2_hidden @ D @ B ) & 
% 0.60/0.87                   ( ![E:$i]:
% 0.60/0.87                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.60/0.87                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.60/0.87            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.60/0.87    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.60/0.87  thf('1', plain,
% 0.60/0.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.87  thf(dt_k2_relset_1, axiom,
% 0.60/0.87    (![A:$i,B:$i,C:$i]:
% 0.60/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.87       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.60/0.87  thf('2', plain,
% 0.60/0.87      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.60/0.87         ((m1_subset_1 @ (k2_relset_1 @ X21 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.60/0.87          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.60/0.87      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.60/0.87  thf('3', plain,
% 0.60/0.87      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 0.60/0.87        (k1_zfmisc_1 @ sk_B))),
% 0.60/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.87  thf('4', plain,
% 0.60/0.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.87  thf(redefinition_k2_relset_1, axiom,
% 0.60/0.87    (![A:$i,B:$i,C:$i]:
% 0.60/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.87       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.60/0.87  thf('5', plain,
% 0.60/0.87      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.60/0.87         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.60/0.87          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.60/0.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.60/0.87  thf('6', plain,
% 0.60/0.87      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.60/0.87      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.87  thf('7', plain,
% 0.60/0.87      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.60/0.87      inference('demod', [status(thm)], ['3', '6'])).
% 0.60/0.87  thf(l3_subset_1, axiom,
% 0.60/0.87    (![A:$i,B:$i]:
% 0.60/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.87       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.60/0.87  thf('8', plain,
% 0.60/0.87      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.87         (~ (r2_hidden @ X8 @ X9)
% 0.60/0.87          | (r2_hidden @ X8 @ X10)
% 0.60/0.87          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.60/0.87      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.60/0.87  thf('9', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.60/0.87      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.87  thf('10', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 0.60/0.87          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_B))),
% 0.60/0.87      inference('sup-', [status(thm)], ['0', '9'])).
% 0.60/0.87  thf('11', plain,
% 0.60/0.87      (![X1 : $i, X3 : $i]:
% 0.60/0.87         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.60/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.87  thf('12', plain,
% 0.60/0.87      (((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)
% 0.60/0.87        | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.60/0.87      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.87  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.60/0.87      inference('simplify', [status(thm)], ['12'])).
% 0.60/0.87  thf(d10_xboole_0, axiom,
% 0.60/0.87    (![A:$i,B:$i]:
% 0.60/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.87  thf('14', plain,
% 0.60/0.87      (![X4 : $i, X6 : $i]:
% 0.60/0.87         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.60/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.87  thf('15', plain,
% 0.60/0.87      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.60/0.87        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.60/0.87      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.87  thf('16', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.87  thf('17', plain,
% 0.60/0.87      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.60/0.87      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.87  thf('18', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.60/0.87      inference('demod', [status(thm)], ['16', '17'])).
% 0.60/0.87  thf('19', plain, (~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.60/0.87      inference('simplify_reflect-', [status(thm)], ['15', '18'])).
% 0.60/0.87  thf('20', plain,
% 0.60/0.87      (![X1 : $i, X3 : $i]:
% 0.60/0.87         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.60/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.87  thf('21', plain,
% 0.60/0.87      (![X38 : $i]:
% 0.60/0.87         (~ (r2_hidden @ X38 @ sk_B)
% 0.60/0.87          | ((X38) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X38))))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.87  thf('22', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         ((r1_tarski @ sk_B @ X0)
% 0.60/0.87          | ((sk_C @ X0 @ sk_B)
% 0.60/0.87              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.60/0.87      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.87  thf('23', plain,
% 0.60/0.87      (![X1 : $i, X3 : $i]:
% 0.60/0.87         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.60/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.87  thf('24', plain,
% 0.60/0.87      (![X38 : $i]:
% 0.60/0.87         (~ (r2_hidden @ X38 @ sk_B) | (r2_hidden @ (sk_E @ X38) @ sk_A))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.87  thf('25', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         ((r1_tarski @ sk_B @ X0)
% 0.60/0.87          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.60/0.87      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.87  thf('26', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.60/0.87      inference('simplify', [status(thm)], ['12'])).
% 0.60/0.87  thf(d1_funct_2, axiom,
% 0.60/0.87    (![A:$i,B:$i,C:$i]:
% 0.60/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.87       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.87           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.60/0.87             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.60/0.87         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.87           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.60/0.87             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.60/0.87  thf(zf_stmt_1, axiom,
% 0.60/0.87    (![B:$i,A:$i]:
% 0.60/0.87     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.87       ( zip_tseitin_0 @ B @ A ) ))).
% 0.60/0.87  thf('27', plain,
% 0.60/0.87      (![X30 : $i, X31 : $i]:
% 0.60/0.87         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.60/0.87  thf('28', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.60/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.87  thf('29', plain,
% 0.60/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.87         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.60/0.87      inference('sup+', [status(thm)], ['27', '28'])).
% 0.60/0.87  thf('30', plain,
% 0.60/0.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.87  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.60/0.87  thf(zf_stmt_3, axiom,
% 0.60/0.87    (![C:$i,B:$i,A:$i]:
% 0.60/0.87     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.60/0.87       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.60/0.87  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.60/0.87  thf(zf_stmt_5, axiom,
% 0.60/0.87    (![A:$i,B:$i,C:$i]:
% 0.60/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.87       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.60/0.87         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.87           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.60/0.87             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.60/0.87  thf('31', plain,
% 0.60/0.87      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.60/0.87         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.60/0.87          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.60/0.87          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.87  thf('32', plain,
% 0.60/0.87      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.60/0.87        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.60/0.87      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.87  thf('33', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.60/0.87      inference('sup-', [status(thm)], ['29', '32'])).
% 0.60/0.87  thf('34', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.87  thf('35', plain,
% 0.60/0.87      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.87         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.60/0.87          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.60/0.87          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.87  thf('36', plain,
% 0.60/0.87      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.60/0.87        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.60/0.87      inference('sup-', [status(thm)], ['34', '35'])).
% 0.60/0.87  thf('37', plain,
% 0.60/0.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.87  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.87    (![A:$i,B:$i,C:$i]:
% 0.60/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.87       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.87  thf('38', plain,
% 0.60/0.87      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.60/0.87         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.60/0.87          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.60/0.87      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.87  thf('39', plain,
% 0.60/0.87      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.60/0.87      inference('sup-', [status(thm)], ['37', '38'])).
% 0.60/0.87  thf('40', plain,
% 0.60/0.87      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.60/0.87        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.60/0.87      inference('demod', [status(thm)], ['36', '39'])).
% 0.60/0.87  thf('41', plain,
% 0.60/0.87      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.60/0.87      inference('sup-', [status(thm)], ['33', '40'])).
% 0.60/0.87  thf('42', plain,
% 0.60/0.87      (![X4 : $i, X6 : $i]:
% 0.60/0.87         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.60/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.87  thf('43', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 0.60/0.87          | ~ (r1_tarski @ X0 @ sk_B)
% 0.60/0.87          | ((X0) = (sk_B)))),
% 0.60/0.87      inference('sup-', [status(thm)], ['41', '42'])).
% 0.60/0.87  thf('44', plain,
% 0.60/0.87      ((((k2_relat_1 @ sk_C_2) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.60/0.87      inference('sup-', [status(thm)], ['26', '43'])).
% 0.60/0.87  thf('45', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.60/0.87      inference('demod', [status(thm)], ['16', '17'])).
% 0.60/0.87  thf('46', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.60/0.87      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.60/0.87  thf(d5_funct_1, axiom,
% 0.60/0.87    (![A:$i]:
% 0.60/0.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.87       ( ![B:$i]:
% 0.60/0.87         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.60/0.87           ( ![C:$i]:
% 0.60/0.87             ( ( r2_hidden @ C @ B ) <=>
% 0.60/0.87               ( ?[D:$i]:
% 0.60/0.87                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.60/0.87                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.60/0.87  thf('47', plain,
% 0.60/0.87      (![X12 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.60/0.87         (((X14) != (k2_relat_1 @ X12))
% 0.60/0.87          | (r2_hidden @ X16 @ X14)
% 0.60/0.87          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 0.60/0.87          | ((X16) != (k1_funct_1 @ X12 @ X17))
% 0.60/0.87          | ~ (v1_funct_1 @ X12)
% 0.60/0.87          | ~ (v1_relat_1 @ X12))),
% 0.60/0.87      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.87  thf('48', plain,
% 0.60/0.87      (![X12 : $i, X17 : $i]:
% 0.60/0.87         (~ (v1_relat_1 @ X12)
% 0.60/0.87          | ~ (v1_funct_1 @ X12)
% 0.60/0.87          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 0.60/0.87          | (r2_hidden @ (k1_funct_1 @ X12 @ X17) @ (k2_relat_1 @ X12)))),
% 0.60/0.87      inference('simplify', [status(thm)], ['47'])).
% 0.60/0.87  thf('49', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         (~ (r2_hidden @ X0 @ sk_A)
% 0.60/0.87          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.60/0.87          | ~ (v1_funct_1 @ sk_C_2)
% 0.60/0.87          | ~ (v1_relat_1 @ sk_C_2))),
% 0.60/0.87      inference('sup-', [status(thm)], ['46', '48'])).
% 0.60/0.87  thf('50', plain, ((v1_funct_1 @ sk_C_2)),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.87  thf('51', plain,
% 0.60/0.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.87  thf(cc1_relset_1, axiom,
% 0.60/0.87    (![A:$i,B:$i,C:$i]:
% 0.60/0.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.87       ( v1_relat_1 @ C ) ))).
% 0.60/0.87  thf('52', plain,
% 0.60/0.87      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.60/0.87         ((v1_relat_1 @ X18)
% 0.60/0.87          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.60/0.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.87  thf('53', plain, ((v1_relat_1 @ sk_C_2)),
% 0.60/0.87      inference('sup-', [status(thm)], ['51', '52'])).
% 0.60/0.87  thf('54', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         (~ (r2_hidden @ X0 @ sk_A)
% 0.60/0.87          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.60/0.87      inference('demod', [status(thm)], ['49', '50', '53'])).
% 0.60/0.87  thf('55', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         ((r1_tarski @ sk_B @ X0)
% 0.60/0.87          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.60/0.87             (k2_relat_1 @ sk_C_2)))),
% 0.60/0.87      inference('sup-', [status(thm)], ['25', '54'])).
% 0.60/0.87  thf('56', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 0.60/0.87          | (r1_tarski @ sk_B @ X0)
% 0.60/0.87          | (r1_tarski @ sk_B @ X0))),
% 0.60/0.87      inference('sup+', [status(thm)], ['22', '55'])).
% 0.60/0.87  thf('57', plain,
% 0.60/0.87      (![X0 : $i]:
% 0.60/0.87         ((r1_tarski @ sk_B @ X0)
% 0.60/0.87          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 0.60/0.87      inference('simplify', [status(thm)], ['56'])).
% 0.60/0.87  thf('58', plain,
% 0.60/0.87      (![X1 : $i, X3 : $i]:
% 0.60/0.87         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.60/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.87  thf('59', plain,
% 0.60/0.87      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.60/0.87        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 0.60/0.87      inference('sup-', [status(thm)], ['57', '58'])).
% 0.60/0.87  thf('60', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.60/0.87      inference('simplify', [status(thm)], ['59'])).
% 0.60/0.87  thf('61', plain, ($false), inference('demod', [status(thm)], ['19', '60'])).
% 0.60/0.87  
% 0.60/0.87  % SZS output end Refutation
% 0.60/0.87  
% 0.69/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
