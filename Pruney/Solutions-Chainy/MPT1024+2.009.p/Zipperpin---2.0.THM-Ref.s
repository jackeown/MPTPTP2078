%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yk2tYg2xQY

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:35 EST 2020

% Result     : Theorem 10.03s
% Output     : Refutation 10.03s
% Verified   : 
% Statistics : Number of formulae       :  206 (10366 expanded)
%              Number of leaves         :   42 (3100 expanded)
%              Depth                    :   26
%              Number of atoms          : 1516 (138133 expanded)
%              Number of equality atoms :  128 (5828 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 != k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ( X40 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,(
    ! [X39: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X39: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X30 @ X28 ) @ X28 )
      | ( ( k1_relset_1 @ X28 @ X29 @ X30 )
        = X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = X1 )
      | ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X30 )
       != X28 )
      | ~ ( r2_hidden @ X31 @ X28 )
      | ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 @ X30 ) ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
       != X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ) @ ( sk_E @ ( sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X30 @ X28 ) @ X32 ) @ X30 )
      | ( ( k1_relset_1 @ X28 @ X29 @ X30 )
        = X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('42',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('43',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['41','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('50',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','68'])).

thf('70',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_A )
      | ~ ( r2_hidden @ X41 @ sk_C )
      | ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('73',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['65','66'])).

thf('76',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['74','75'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('77',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X16 )
      | ( X17
        = ( k1_funct_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( sk_E_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['65','66'])).

thf('80',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( sk_E_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('83',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['65','66'])).

thf('86',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_1 != sk_E_1 ) ),
    inference(demod,[status(thm)],['71','81','86'])).

thf('88',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','88'])).

thf('90',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('91',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['87'])).

thf('92',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_A )
      | ~ ( r2_hidden @ X41 @ sk_C )
      | ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( sk_E_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('99',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ),
    inference(demod,[status(thm)],['84','85'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_E_1 != sk_E_1 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('103',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('107',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['87'])).

thf('109',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 != k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('111',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['87'])).

thf('115',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('118',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('119',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('120',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X1 @ X3 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ sk_D_2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['118','125'])).

thf('127',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_A )
      | ~ ( r2_hidden @ X41 @ sk_C )
      | ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ sk_D_2 ) @ X0 )
      | ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( sk_E_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('130',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ),
    inference(demod,[status(thm)],['84','85'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ sk_D_2 ) @ X0 )
      | ( sk_E_1 != sk_E_1 ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['117','132'])).

thf('134',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('137',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['87'])).

thf('138',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['87'])).

thf('139',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','139'])).

thf('141',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('142',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( sk_A
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['116','142'])).

thf('144',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','144'])).

thf('146',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['105','146'])).

thf('148',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','147'])).

thf('149',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','147'])).

thf('150',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','147'])).

thf('151',plain,(
    r2_hidden @ sk_E_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['4','148','149','150'])).

thf('152',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_A )
      | ~ ( r2_hidden @ X41 @ sk_C )
      | ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['145'])).

thf('154',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X41 @ sk_C )
      | ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('156',plain,(
    ! [X41: $i] :
      ( ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X41 ) )
      | ~ ( r2_hidden @ X41 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','147'])).

thf('158',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','147'])).

thf('159',plain,(
    ! [X41: $i] :
      ( ( sk_E_1 != k1_xboole_0 )
      | ~ ( r2_hidden @ X41 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','147'])).

thf('161',plain,(
    ! [X41: $i] :
      ~ ( r2_hidden @ X41 @ k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['159','160'])).

thf('162',plain,(
    $false ),
    inference('sup-',[status(thm)],['151','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yk2tYg2xQY
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:44:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 10.03/10.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.03/10.29  % Solved by: fo/fo7.sh
% 10.03/10.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.03/10.29  % done 3233 iterations in 9.833s
% 10.03/10.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.03/10.29  % SZS output start Refutation
% 10.03/10.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.03/10.29  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 10.03/10.29  thf(sk_B_type, type, sk_B: $i).
% 10.03/10.29  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 10.03/10.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.03/10.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.03/10.29  thf(sk_A_type, type, sk_A: $i).
% 10.03/10.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.03/10.29  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 10.03/10.29  thf(sk_D_2_type, type, sk_D_2: $i).
% 10.03/10.29  thf(sk_E_1_type, type, sk_E_1: $i).
% 10.03/10.29  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 10.03/10.29  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 10.03/10.29  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 10.03/10.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 10.03/10.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.03/10.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.03/10.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.03/10.29  thf(sk_C_type, type, sk_C: $i).
% 10.03/10.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.03/10.29  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.03/10.29  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 10.03/10.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.03/10.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.03/10.29  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 10.03/10.29  thf(t115_funct_2, conjecture,
% 10.03/10.29    (![A:$i,B:$i,C:$i,D:$i]:
% 10.03/10.29     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.03/10.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.03/10.29       ( ![E:$i]:
% 10.03/10.29         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 10.03/10.29              ( ![F:$i]:
% 10.03/10.29                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 10.03/10.29                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 10.03/10.29  thf(zf_stmt_0, negated_conjecture,
% 10.03/10.29    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 10.03/10.29        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.03/10.29            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.03/10.29          ( ![E:$i]:
% 10.03/10.29            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 10.03/10.29                 ( ![F:$i]:
% 10.03/10.29                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 10.03/10.29                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 10.03/10.29    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 10.03/10.29  thf('0', plain,
% 10.03/10.29      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('1', plain,
% 10.03/10.29      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf(redefinition_k7_relset_1, axiom,
% 10.03/10.29    (![A:$i,B:$i,C:$i,D:$i]:
% 10.03/10.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.03/10.29       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 10.03/10.29  thf('2', plain,
% 10.03/10.29      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 10.03/10.29         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 10.03/10.29          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 10.03/10.29      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 10.03/10.29  thf('3', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 10.03/10.29           = (k9_relat_1 @ sk_D_2 @ X0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['1', '2'])).
% 10.03/10.29  thf('4', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 10.03/10.29      inference('demod', [status(thm)], ['0', '3'])).
% 10.03/10.29  thf(d1_funct_2, axiom,
% 10.03/10.29    (![A:$i,B:$i,C:$i]:
% 10.03/10.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.03/10.29       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.03/10.29           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 10.03/10.29             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 10.03/10.29         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.03/10.29           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 10.03/10.29             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 10.03/10.29  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 10.03/10.29  thf(zf_stmt_2, axiom,
% 10.03/10.29    (![C:$i,B:$i,A:$i]:
% 10.03/10.29     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 10.03/10.29       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 10.03/10.29  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 10.03/10.29  thf(zf_stmt_4, axiom,
% 10.03/10.29    (![B:$i,A:$i]:
% 10.03/10.29     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.03/10.29       ( zip_tseitin_0 @ B @ A ) ))).
% 10.03/10.29  thf(zf_stmt_5, axiom,
% 10.03/10.29    (![A:$i,B:$i,C:$i]:
% 10.03/10.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.03/10.29       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 10.03/10.29         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.03/10.29           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 10.03/10.29             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 10.03/10.29  thf('5', plain,
% 10.03/10.29      (![X38 : $i, X39 : $i, X40 : $i]:
% 10.03/10.29         (((X38) != (k1_xboole_0))
% 10.03/10.29          | ((X39) = (k1_xboole_0))
% 10.03/10.29          | (v1_funct_2 @ X40 @ X39 @ X38)
% 10.03/10.29          | ((X40) != (k1_xboole_0))
% 10.03/10.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.03/10.29  thf('6', plain,
% 10.03/10.29      (![X39 : $i]:
% 10.03/10.29         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 10.03/10.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ k1_xboole_0)))
% 10.03/10.29          | (v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0)
% 10.03/10.29          | ((X39) = (k1_xboole_0)))),
% 10.03/10.29      inference('simplify', [status(thm)], ['5'])).
% 10.03/10.29  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 10.03/10.29  thf('7', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 10.03/10.29      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.03/10.29  thf(t3_subset, axiom,
% 10.03/10.29    (![A:$i,B:$i]:
% 10.03/10.29     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.03/10.29  thf('8', plain,
% 10.03/10.29      (![X4 : $i, X6 : $i]:
% 10.03/10.29         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 10.03/10.29      inference('cnf', [status(esa)], [t3_subset])).
% 10.03/10.29  thf('9', plain,
% 10.03/10.29      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['7', '8'])).
% 10.03/10.29  thf('10', plain,
% 10.03/10.29      (![X39 : $i]:
% 10.03/10.29         ((v1_funct_2 @ k1_xboole_0 @ X39 @ k1_xboole_0)
% 10.03/10.29          | ((X39) = (k1_xboole_0)))),
% 10.03/10.29      inference('demod', [status(thm)], ['6', '9'])).
% 10.03/10.29  thf('11', plain,
% 10.03/10.29      (![X35 : $i, X36 : $i, X37 : $i]:
% 10.03/10.29         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 10.03/10.29          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 10.03/10.29          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 10.03/10.29  thf('12', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         (((X0) = (k1_xboole_0))
% 10.03/10.29          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 10.03/10.29          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 10.03/10.29      inference('sup-', [status(thm)], ['10', '11'])).
% 10.03/10.29  thf('13', plain,
% 10.03/10.29      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['7', '8'])).
% 10.03/10.29  thf(redefinition_k1_relset_1, axiom,
% 10.03/10.29    (![A:$i,B:$i,C:$i]:
% 10.03/10.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.03/10.29       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.03/10.29  thf('14', plain,
% 10.03/10.29      (![X21 : $i, X22 : $i, X23 : $i]:
% 10.03/10.29         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 10.03/10.29          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 10.03/10.29      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.03/10.29  thf('15', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i]:
% 10.03/10.29         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['13', '14'])).
% 10.03/10.29  thf('16', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         (((X0) = (k1_xboole_0))
% 10.03/10.29          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 10.03/10.29          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 10.03/10.29      inference('demod', [status(thm)], ['12', '15'])).
% 10.03/10.29  thf('17', plain,
% 10.03/10.29      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['7', '8'])).
% 10.03/10.29  thf(t22_relset_1, axiom,
% 10.03/10.29    (![A:$i,B:$i,C:$i]:
% 10.03/10.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 10.03/10.29       ( ( ![D:$i]:
% 10.03/10.29           ( ~( ( r2_hidden @ D @ B ) & 
% 10.03/10.29                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 10.03/10.29         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 10.03/10.29  thf('18', plain,
% 10.03/10.29      (![X28 : $i, X29 : $i, X30 : $i]:
% 10.03/10.29         ((r2_hidden @ (sk_D_1 @ X30 @ X28) @ X28)
% 10.03/10.29          | ((k1_relset_1 @ X28 @ X29 @ X30) = (X28))
% 10.03/10.29          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 10.03/10.29      inference('cnf', [status(esa)], [t22_relset_1])).
% 10.03/10.29  thf('19', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i]:
% 10.03/10.29         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (X1))
% 10.03/10.29          | (r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X1) @ X1))),
% 10.03/10.29      inference('sup-', [status(thm)], ['17', '18'])).
% 10.03/10.29  thf('20', plain,
% 10.03/10.29      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['7', '8'])).
% 10.03/10.29  thf(l3_subset_1, axiom,
% 10.03/10.29    (![A:$i,B:$i]:
% 10.03/10.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.03/10.29       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 10.03/10.29  thf('21', plain,
% 10.03/10.29      (![X1 : $i, X2 : $i, X3 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X1 @ X2)
% 10.03/10.29          | (r2_hidden @ X1 @ X3)
% 10.03/10.29          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 10.03/10.29      inference('cnf', [status(esa)], [l3_subset_1])).
% 10.03/10.29  thf('22', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i]:
% 10.03/10.29         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['20', '21'])).
% 10.03/10.29  thf('23', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i]:
% 10.03/10.29         (((k1_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 10.03/10.29          | (r2_hidden @ (sk_D_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['19', '22'])).
% 10.03/10.29  thf('24', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i]:
% 10.03/10.29         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['13', '14'])).
% 10.03/10.29  thf('25', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 10.03/10.29          | (r2_hidden @ (sk_D_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 10.03/10.29      inference('demod', [status(thm)], ['23', '24'])).
% 10.03/10.29  thf('26', plain,
% 10.03/10.29      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['7', '8'])).
% 10.03/10.29  thf('27', plain,
% 10.03/10.29      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 10.03/10.29         (((k1_relset_1 @ X28 @ X29 @ X30) != (X28))
% 10.03/10.29          | ~ (r2_hidden @ X31 @ X28)
% 10.03/10.29          | (r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31 @ X30)) @ X30)
% 10.03/10.29          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 10.03/10.29      inference('cnf', [status(esa)], [t22_relset_1])).
% 10.03/10.29  thf('28', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.03/10.29         ((r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 10.03/10.29           k1_xboole_0)
% 10.03/10.29          | ~ (r2_hidden @ X2 @ X1)
% 10.03/10.29          | ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) != (X1)))),
% 10.03/10.29      inference('sup-', [status(thm)], ['26', '27'])).
% 10.03/10.29  thf('29', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i]:
% 10.03/10.29         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['13', '14'])).
% 10.03/10.29  thf('30', plain,
% 10.03/10.29      (![X1 : $i, X2 : $i]:
% 10.03/10.29         ((r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 10.03/10.29           k1_xboole_0)
% 10.03/10.29          | ~ (r2_hidden @ X2 @ X1)
% 10.03/10.29          | ((k1_relat_1 @ k1_xboole_0) != (X1)))),
% 10.03/10.29      inference('demod', [status(thm)], ['28', '29'])).
% 10.03/10.29  thf('31', plain,
% 10.03/10.29      (![X2 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X2 @ (k1_relat_1 @ k1_xboole_0))
% 10.03/10.29          | (r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 10.03/10.29             k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['30'])).
% 10.03/10.29  thf('32', plain,
% 10.03/10.29      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 10.03/10.29        | (r2_hidden @ 
% 10.03/10.29           (k4_tarski @ (sk_D_1 @ k1_xboole_0 @ k1_xboole_0) @ 
% 10.03/10.29            (sk_E @ (sk_D_1 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 10.03/10.29           k1_xboole_0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['25', '31'])).
% 10.03/10.29  thf('33', plain,
% 10.03/10.29      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i]:
% 10.03/10.29         (~ (r2_hidden @ (k4_tarski @ (sk_D_1 @ X30 @ X28) @ X32) @ X30)
% 10.03/10.29          | ((k1_relset_1 @ X28 @ X29 @ X30) = (X28))
% 10.03/10.29          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 10.03/10.29      inference('cnf', [status(esa)], [t22_relset_1])).
% 10.03/10.29  thf('34', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 10.03/10.29          | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 10.03/10.29               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))
% 10.03/10.29          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 10.03/10.29      inference('sup-', [status(thm)], ['32', '33'])).
% 10.03/10.29  thf('35', plain,
% 10.03/10.29      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['7', '8'])).
% 10.03/10.29  thf('36', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i]:
% 10.03/10.29         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['13', '14'])).
% 10.03/10.29  thf('37', plain,
% 10.03/10.29      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 10.03/10.29        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 10.03/10.29      inference('demod', [status(thm)], ['34', '35', '36'])).
% 10.03/10.29  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['37'])).
% 10.03/10.29  thf('39', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         (((X0) = (k1_xboole_0))
% 10.03/10.29          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 10.03/10.29          | ((X0) = (k1_xboole_0)))),
% 10.03/10.29      inference('demod', [status(thm)], ['16', '38'])).
% 10.03/10.29  thf('40', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 10.03/10.29          | ((X0) = (k1_xboole_0)))),
% 10.03/10.29      inference('simplify', [status(thm)], ['39'])).
% 10.03/10.29  thf('41', plain,
% 10.03/10.29      (![X33 : $i, X34 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_4])).
% 10.03/10.29  thf('42', plain,
% 10.03/10.29      (![X33 : $i, X34 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_4])).
% 10.03/10.29  thf('43', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 10.03/10.29      inference('simplify', [status(thm)], ['42'])).
% 10.03/10.29  thf('44', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 10.03/10.29      inference('sup+', [status(thm)], ['41', '43'])).
% 10.03/10.29  thf('45', plain,
% 10.03/10.29      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('46', plain,
% 10.03/10.29      (![X38 : $i, X39 : $i, X40 : $i]:
% 10.03/10.29         (~ (zip_tseitin_0 @ X38 @ X39)
% 10.03/10.29          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 10.03/10.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.03/10.29  thf('47', plain,
% 10.03/10.29      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 10.03/10.29        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.03/10.29      inference('sup-', [status(thm)], ['45', '46'])).
% 10.03/10.29  thf('48', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ sk_A @ X0) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 10.03/10.29      inference('sup-', [status(thm)], ['44', '47'])).
% 10.03/10.29  thf('49', plain,
% 10.03/10.29      (![X33 : $i, X34 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_4])).
% 10.03/10.29  thf('50', plain,
% 10.03/10.29      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 10.03/10.29        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.03/10.29      inference('sup-', [status(thm)], ['45', '46'])).
% 10.03/10.29  thf('51', plain,
% 10.03/10.29      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 10.03/10.29      inference('sup-', [status(thm)], ['49', '50'])).
% 10.03/10.29  thf('52', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('53', plain,
% 10.03/10.29      (![X35 : $i, X36 : $i, X37 : $i]:
% 10.03/10.29         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 10.03/10.29          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 10.03/10.29          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_2])).
% 10.03/10.29  thf('54', plain,
% 10.03/10.29      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 10.03/10.29        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 10.03/10.29      inference('sup-', [status(thm)], ['52', '53'])).
% 10.03/10.29  thf('55', plain,
% 10.03/10.29      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('56', plain,
% 10.03/10.29      (![X21 : $i, X22 : $i, X23 : $i]:
% 10.03/10.29         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 10.03/10.29          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 10.03/10.29      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.03/10.29  thf('57', plain,
% 10.03/10.29      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 10.03/10.29      inference('sup-', [status(thm)], ['55', '56'])).
% 10.03/10.29  thf('58', plain,
% 10.03/10.29      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 10.03/10.29        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 10.03/10.29      inference('demod', [status(thm)], ['54', '57'])).
% 10.03/10.29  thf('59', plain,
% 10.03/10.29      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 10.03/10.29      inference('sup-', [status(thm)], ['51', '58'])).
% 10.03/10.29  thf('60', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 10.03/10.29      inference('demod', [status(thm)], ['0', '3'])).
% 10.03/10.29  thf(t143_relat_1, axiom,
% 10.03/10.29    (![A:$i,B:$i,C:$i]:
% 10.03/10.29     ( ( v1_relat_1 @ C ) =>
% 10.03/10.29       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 10.03/10.29         ( ?[D:$i]:
% 10.03/10.29           ( ( r2_hidden @ D @ B ) & 
% 10.03/10.29             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 10.03/10.29             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 10.03/10.29  thf('61', plain,
% 10.03/10.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 10.03/10.29          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ (k1_relat_1 @ X14))
% 10.03/10.29          | ~ (v1_relat_1 @ X14))),
% 10.03/10.29      inference('cnf', [status(esa)], [t143_relat_1])).
% 10.03/10.29  thf('62', plain,
% 10.03/10.29      ((~ (v1_relat_1 @ sk_D_2)
% 10.03/10.29        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2)))),
% 10.03/10.29      inference('sup-', [status(thm)], ['60', '61'])).
% 10.03/10.29  thf('63', plain,
% 10.03/10.29      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf(cc2_relat_1, axiom,
% 10.03/10.29    (![A:$i]:
% 10.03/10.29     ( ( v1_relat_1 @ A ) =>
% 10.03/10.29       ( ![B:$i]:
% 10.03/10.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 10.03/10.29  thf('64', plain,
% 10.03/10.29      (![X7 : $i, X8 : $i]:
% 10.03/10.29         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 10.03/10.29          | (v1_relat_1 @ X7)
% 10.03/10.29          | ~ (v1_relat_1 @ X8))),
% 10.03/10.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.03/10.29  thf('65', plain,
% 10.03/10.29      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 10.03/10.29      inference('sup-', [status(thm)], ['63', '64'])).
% 10.03/10.29  thf(fc6_relat_1, axiom,
% 10.03/10.29    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 10.03/10.29  thf('66', plain,
% 10.03/10.29      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 10.03/10.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 10.03/10.29  thf('67', plain, ((v1_relat_1 @ sk_D_2)),
% 10.03/10.29      inference('demod', [status(thm)], ['65', '66'])).
% 10.03/10.29  thf('68', plain,
% 10.03/10.29      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 10.03/10.29      inference('demod', [status(thm)], ['62', '67'])).
% 10.03/10.29  thf('69', plain,
% 10.03/10.29      (((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_A)
% 10.03/10.29        | ((sk_B) = (k1_xboole_0)))),
% 10.03/10.29      inference('sup+', [status(thm)], ['59', '68'])).
% 10.03/10.29  thf('70', plain,
% 10.03/10.29      (![X41 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X41 @ sk_A)
% 10.03/10.29          | ~ (r2_hidden @ X41 @ sk_C)
% 10.03/10.29          | ((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X41)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('71', plain,
% 10.03/10.29      ((((sk_B) = (k1_xboole_0))
% 10.03/10.29        | ((sk_E_1) != (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1)))
% 10.03/10.29        | ~ (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C))),
% 10.03/10.29      inference('sup-', [status(thm)], ['69', '70'])).
% 10.03/10.29  thf('72', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 10.03/10.29      inference('demod', [status(thm)], ['0', '3'])).
% 10.03/10.29  thf('73', plain,
% 10.03/10.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 10.03/10.29          | (r2_hidden @ (k4_tarski @ (sk_D @ X14 @ X12 @ X13) @ X13) @ X14)
% 10.03/10.29          | ~ (v1_relat_1 @ X14))),
% 10.03/10.29      inference('cnf', [status(esa)], [t143_relat_1])).
% 10.03/10.29  thf('74', plain,
% 10.03/10.29      ((~ (v1_relat_1 @ sk_D_2)
% 10.03/10.29        | (r2_hidden @ 
% 10.03/10.29           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1) @ sk_D_2))),
% 10.03/10.29      inference('sup-', [status(thm)], ['72', '73'])).
% 10.03/10.29  thf('75', plain, ((v1_relat_1 @ sk_D_2)),
% 10.03/10.29      inference('demod', [status(thm)], ['65', '66'])).
% 10.03/10.29  thf('76', plain,
% 10.03/10.29      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1) @ 
% 10.03/10.29        sk_D_2)),
% 10.03/10.29      inference('demod', [status(thm)], ['74', '75'])).
% 10.03/10.29  thf(t8_funct_1, axiom,
% 10.03/10.29    (![A:$i,B:$i,C:$i]:
% 10.03/10.29     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 10.03/10.29       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 10.03/10.29         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 10.03/10.29           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 10.03/10.29  thf('77', plain,
% 10.03/10.29      (![X15 : $i, X16 : $i, X17 : $i]:
% 10.03/10.29         (~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X16)
% 10.03/10.29          | ((X17) = (k1_funct_1 @ X16 @ X15))
% 10.03/10.29          | ~ (v1_funct_1 @ X16)
% 10.03/10.29          | ~ (v1_relat_1 @ X16))),
% 10.03/10.29      inference('cnf', [status(esa)], [t8_funct_1])).
% 10.03/10.29  thf('78', plain,
% 10.03/10.29      ((~ (v1_relat_1 @ sk_D_2)
% 10.03/10.29        | ~ (v1_funct_1 @ sk_D_2)
% 10.03/10.29        | ((sk_E_1) = (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1))))),
% 10.03/10.29      inference('sup-', [status(thm)], ['76', '77'])).
% 10.03/10.29  thf('79', plain, ((v1_relat_1 @ sk_D_2)),
% 10.03/10.29      inference('demod', [status(thm)], ['65', '66'])).
% 10.03/10.29  thf('80', plain, ((v1_funct_1 @ sk_D_2)),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('81', plain,
% 10.03/10.29      (((sk_E_1) = (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1)))),
% 10.03/10.29      inference('demod', [status(thm)], ['78', '79', '80'])).
% 10.03/10.29  thf('82', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 10.03/10.29      inference('demod', [status(thm)], ['0', '3'])).
% 10.03/10.29  thf('83', plain,
% 10.03/10.29      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 10.03/10.29          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 10.03/10.29          | ~ (v1_relat_1 @ X14))),
% 10.03/10.29      inference('cnf', [status(esa)], [t143_relat_1])).
% 10.03/10.29  thf('84', plain,
% 10.03/10.29      ((~ (v1_relat_1 @ sk_D_2)
% 10.03/10.29        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C))),
% 10.03/10.29      inference('sup-', [status(thm)], ['82', '83'])).
% 10.03/10.29  thf('85', plain, ((v1_relat_1 @ sk_D_2)),
% 10.03/10.29      inference('demod', [status(thm)], ['65', '66'])).
% 10.03/10.29  thf('86', plain, ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C)),
% 10.03/10.29      inference('demod', [status(thm)], ['84', '85'])).
% 10.03/10.29  thf('87', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E_1) != (sk_E_1)))),
% 10.03/10.29      inference('demod', [status(thm)], ['71', '81', '86'])).
% 10.03/10.29  thf('88', plain, (((sk_B) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['87'])).
% 10.03/10.29  thf('89', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ sk_A @ X0)
% 10.03/10.29          | (zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A))),
% 10.03/10.29      inference('demod', [status(thm)], ['48', '88'])).
% 10.03/10.29  thf('90', plain,
% 10.03/10.29      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 10.03/10.29        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 10.03/10.29      inference('demod', [status(thm)], ['54', '57'])).
% 10.03/10.29  thf('91', plain, (((sk_B) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['87'])).
% 10.03/10.29  thf('92', plain,
% 10.03/10.29      ((~ (zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 10.03/10.29        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 10.03/10.29      inference('demod', [status(thm)], ['90', '91'])).
% 10.03/10.29  thf('93', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 10.03/10.29      inference('sup-', [status(thm)], ['89', '92'])).
% 10.03/10.29  thf('94', plain,
% 10.03/10.29      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 10.03/10.29      inference('demod', [status(thm)], ['62', '67'])).
% 10.03/10.29  thf('95', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_A)
% 10.03/10.29          | (zip_tseitin_0 @ sk_A @ X0))),
% 10.03/10.29      inference('sup+', [status(thm)], ['93', '94'])).
% 10.03/10.29  thf('96', plain,
% 10.03/10.29      (![X41 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X41 @ sk_A)
% 10.03/10.29          | ~ (r2_hidden @ X41 @ sk_C)
% 10.03/10.29          | ((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X41)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('97', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ sk_A @ X0)
% 10.03/10.29          | ((sk_E_1)
% 10.03/10.29              != (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1)))
% 10.03/10.29          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C))),
% 10.03/10.29      inference('sup-', [status(thm)], ['95', '96'])).
% 10.03/10.29  thf('98', plain,
% 10.03/10.29      (((sk_E_1) = (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1)))),
% 10.03/10.29      inference('demod', [status(thm)], ['78', '79', '80'])).
% 10.03/10.29  thf('99', plain, ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C)),
% 10.03/10.29      inference('demod', [status(thm)], ['84', '85'])).
% 10.03/10.29  thf('100', plain,
% 10.03/10.29      (![X0 : $i]: ((zip_tseitin_0 @ sk_A @ X0) | ((sk_E_1) != (sk_E_1)))),
% 10.03/10.29      inference('demod', [status(thm)], ['97', '98', '99'])).
% 10.03/10.29  thf('101', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 10.03/10.29      inference('simplify', [status(thm)], ['100'])).
% 10.03/10.29  thf('102', plain,
% 10.03/10.29      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['7', '8'])).
% 10.03/10.29  thf('103', plain,
% 10.03/10.29      (![X38 : $i, X39 : $i, X40 : $i]:
% 10.03/10.29         (~ (zip_tseitin_0 @ X38 @ X39)
% 10.03/10.29          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 10.03/10.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.03/10.29  thf('104', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i]:
% 10.03/10.29         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 10.03/10.29      inference('sup-', [status(thm)], ['102', '103'])).
% 10.03/10.29  thf('105', plain, (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ sk_A @ X0)),
% 10.03/10.29      inference('sup-', [status(thm)], ['101', '104'])).
% 10.03/10.29  thf('106', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['37'])).
% 10.03/10.29  thf('107', plain,
% 10.03/10.29      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('108', plain, (((sk_B) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['87'])).
% 10.03/10.29  thf('109', plain,
% 10.03/10.29      ((m1_subset_1 @ sk_D_2 @ 
% 10.03/10.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 10.03/10.29      inference('demod', [status(thm)], ['107', '108'])).
% 10.03/10.29  thf('110', plain,
% 10.03/10.29      (![X38 : $i, X39 : $i, X40 : $i]:
% 10.03/10.29         (((X38) != (k1_xboole_0))
% 10.03/10.29          | ((X39) = (k1_xboole_0))
% 10.03/10.29          | ((X40) = (k1_xboole_0))
% 10.03/10.29          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 10.03/10.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.03/10.29  thf('111', plain,
% 10.03/10.29      (![X39 : $i, X40 : $i]:
% 10.03/10.29         (~ (m1_subset_1 @ X40 @ 
% 10.03/10.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ k1_xboole_0)))
% 10.03/10.29          | ~ (v1_funct_2 @ X40 @ X39 @ k1_xboole_0)
% 10.03/10.29          | ((X40) = (k1_xboole_0))
% 10.03/10.29          | ((X39) = (k1_xboole_0)))),
% 10.03/10.29      inference('simplify', [status(thm)], ['110'])).
% 10.03/10.29  thf('112', plain,
% 10.03/10.29      ((((sk_A) = (k1_xboole_0))
% 10.03/10.29        | ((sk_D_2) = (k1_xboole_0))
% 10.03/10.29        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['109', '111'])).
% 10.03/10.29  thf('113', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('114', plain, (((sk_B) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['87'])).
% 10.03/10.29  thf('115', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)),
% 10.03/10.29      inference('demod', [status(thm)], ['113', '114'])).
% 10.03/10.29  thf('116', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 10.03/10.29      inference('demod', [status(thm)], ['112', '115'])).
% 10.03/10.29  thf('117', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 10.03/10.29      inference('demod', [status(thm)], ['112', '115'])).
% 10.03/10.29  thf('118', plain,
% 10.03/10.29      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 10.03/10.29      inference('demod', [status(thm)], ['62', '67'])).
% 10.03/10.29  thf('119', plain,
% 10.03/10.29      (![X33 : $i, X34 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_4])).
% 10.03/10.29  thf('120', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 10.03/10.29      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.03/10.29  thf('121', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.03/10.29         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 10.03/10.29      inference('sup+', [status(thm)], ['119', '120'])).
% 10.03/10.29  thf('122', plain,
% 10.03/10.29      (![X4 : $i, X6 : $i]:
% 10.03/10.29         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 10.03/10.29      inference('cnf', [status(esa)], [t3_subset])).
% 10.03/10.29  thf('123', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ X1 @ X2) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 10.03/10.29      inference('sup-', [status(thm)], ['121', '122'])).
% 10.03/10.29  thf('124', plain,
% 10.03/10.29      (![X1 : $i, X2 : $i, X3 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X1 @ X2)
% 10.03/10.29          | (r2_hidden @ X1 @ X3)
% 10.03/10.29          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 10.03/10.29      inference('cnf', [status(esa)], [l3_subset_1])).
% 10.03/10.29  thf('125', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ X1 @ X3)
% 10.03/10.29          | (r2_hidden @ X2 @ X0)
% 10.03/10.29          | ~ (r2_hidden @ X2 @ X1))),
% 10.03/10.29      inference('sup-', [status(thm)], ['123', '124'])).
% 10.03/10.29  thf('126', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i]:
% 10.03/10.29         ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ X0)
% 10.03/10.29          | (zip_tseitin_0 @ (k1_relat_1 @ sk_D_2) @ X1))),
% 10.03/10.29      inference('sup-', [status(thm)], ['118', '125'])).
% 10.03/10.29  thf('127', plain,
% 10.03/10.29      (![X41 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X41 @ sk_A)
% 10.03/10.29          | ~ (r2_hidden @ X41 @ sk_C)
% 10.03/10.29          | ((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X41)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('128', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ (k1_relat_1 @ sk_D_2) @ X0)
% 10.03/10.29          | ((sk_E_1)
% 10.03/10.29              != (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1)))
% 10.03/10.29          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C))),
% 10.03/10.29      inference('sup-', [status(thm)], ['126', '127'])).
% 10.03/10.29  thf('129', plain,
% 10.03/10.29      (((sk_E_1) = (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1)))),
% 10.03/10.29      inference('demod', [status(thm)], ['78', '79', '80'])).
% 10.03/10.29  thf('130', plain, ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C)),
% 10.03/10.29      inference('demod', [status(thm)], ['84', '85'])).
% 10.03/10.29  thf('131', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ (k1_relat_1 @ sk_D_2) @ X0) | ((sk_E_1) != (sk_E_1)))),
% 10.03/10.29      inference('demod', [status(thm)], ['128', '129', '130'])).
% 10.03/10.29  thf('132', plain, (![X0 : $i]: (zip_tseitin_0 @ (k1_relat_1 @ sk_D_2) @ X0)),
% 10.03/10.29      inference('simplify', [status(thm)], ['131'])).
% 10.03/10.29  thf('133', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 10.03/10.29          | ((sk_A) = (k1_xboole_0)))),
% 10.03/10.29      inference('sup+', [status(thm)], ['117', '132'])).
% 10.03/10.29  thf('134', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['37'])).
% 10.03/10.29  thf('135', plain,
% 10.03/10.29      (![X0 : $i]:
% 10.03/10.29         ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_xboole_0)))),
% 10.03/10.29      inference('demod', [status(thm)], ['133', '134'])).
% 10.03/10.29  thf('136', plain,
% 10.03/10.29      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 10.03/10.29        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.03/10.29      inference('sup-', [status(thm)], ['45', '46'])).
% 10.03/10.29  thf('137', plain, (((sk_B) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['87'])).
% 10.03/10.29  thf('138', plain, (((sk_B) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['87'])).
% 10.03/10.29  thf('139', plain,
% 10.03/10.29      (((zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 10.03/10.29        | ~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A))),
% 10.03/10.29      inference('demod', [status(thm)], ['136', '137', '138'])).
% 10.03/10.29  thf('140', plain,
% 10.03/10.29      ((((sk_A) = (k1_xboole_0))
% 10.03/10.29        | (zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A))),
% 10.03/10.29      inference('sup-', [status(thm)], ['135', '139'])).
% 10.03/10.29  thf('141', plain,
% 10.03/10.29      ((~ (zip_tseitin_1 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 10.03/10.29        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 10.03/10.29      inference('demod', [status(thm)], ['90', '91'])).
% 10.03/10.29  thf('142', plain,
% 10.03/10.29      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 10.03/10.29      inference('sup-', [status(thm)], ['140', '141'])).
% 10.03/10.29  thf('143', plain,
% 10.03/10.29      ((((sk_A) = (k1_relat_1 @ k1_xboole_0))
% 10.03/10.29        | ((sk_A) = (k1_xboole_0))
% 10.03/10.29        | ((sk_A) = (k1_xboole_0)))),
% 10.03/10.29      inference('sup+', [status(thm)], ['116', '142'])).
% 10.03/10.29  thf('144', plain,
% 10.03/10.29      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ k1_xboole_0)))),
% 10.03/10.29      inference('simplify', [status(thm)], ['143'])).
% 10.03/10.29  thf('145', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 10.03/10.29      inference('sup+', [status(thm)], ['106', '144'])).
% 10.03/10.29  thf('146', plain, (((sk_A) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['145'])).
% 10.03/10.29  thf('147', plain,
% 10.03/10.29      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 10.03/10.29      inference('demod', [status(thm)], ['105', '146'])).
% 10.03/10.29  thf('148', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 10.03/10.29      inference('demod', [status(thm)], ['40', '147'])).
% 10.03/10.29  thf('149', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 10.03/10.29      inference('demod', [status(thm)], ['40', '147'])).
% 10.03/10.29  thf('150', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 10.03/10.29      inference('demod', [status(thm)], ['40', '147'])).
% 10.03/10.29  thf('151', plain, ((r2_hidden @ sk_E_1 @ k1_xboole_0)),
% 10.03/10.29      inference('demod', [status(thm)], ['4', '148', '149', '150'])).
% 10.03/10.29  thf('152', plain,
% 10.03/10.29      (![X41 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X41 @ sk_A)
% 10.03/10.29          | ~ (r2_hidden @ X41 @ sk_C)
% 10.03/10.29          | ((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X41)))),
% 10.03/10.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.03/10.29  thf('153', plain, (((sk_A) = (k1_xboole_0))),
% 10.03/10.29      inference('simplify', [status(thm)], ['145'])).
% 10.03/10.29  thf('154', plain,
% 10.03/10.29      (![X41 : $i]:
% 10.03/10.29         (~ (r2_hidden @ X41 @ k1_xboole_0)
% 10.03/10.29          | ~ (r2_hidden @ X41 @ sk_C)
% 10.03/10.29          | ((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X41)))),
% 10.03/10.29      inference('demod', [status(thm)], ['152', '153'])).
% 10.03/10.29  thf('155', plain,
% 10.03/10.29      (![X0 : $i, X1 : $i]:
% 10.03/10.29         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 10.03/10.29      inference('sup-', [status(thm)], ['20', '21'])).
% 10.03/10.29  thf('156', plain,
% 10.03/10.29      (![X41 : $i]:
% 10.03/10.29         (((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X41))
% 10.03/10.29          | ~ (r2_hidden @ X41 @ k1_xboole_0))),
% 10.03/10.29      inference('clc', [status(thm)], ['154', '155'])).
% 10.03/10.29  thf('157', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 10.03/10.29      inference('demod', [status(thm)], ['40', '147'])).
% 10.03/10.29  thf('158', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 10.03/10.29      inference('demod', [status(thm)], ['40', '147'])).
% 10.03/10.29  thf('159', plain,
% 10.03/10.29      (![X41 : $i]:
% 10.03/10.29         (((sk_E_1) != (k1_xboole_0)) | ~ (r2_hidden @ X41 @ k1_xboole_0))),
% 10.03/10.29      inference('demod', [status(thm)], ['156', '157', '158'])).
% 10.03/10.29  thf('160', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 10.03/10.29      inference('demod', [status(thm)], ['40', '147'])).
% 10.03/10.29  thf('161', plain, (![X41 : $i]: ~ (r2_hidden @ X41 @ k1_xboole_0)),
% 10.03/10.29      inference('simplify_reflect+', [status(thm)], ['159', '160'])).
% 10.03/10.29  thf('162', plain, ($false), inference('sup-', [status(thm)], ['151', '161'])).
% 10.03/10.29  
% 10.03/10.29  % SZS output end Refutation
% 10.03/10.29  
% 10.03/10.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
