%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DJttm3WLQj

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:27 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 168 expanded)
%              Number of leaves         :   40 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  675 (1909 expanded)
%              Number of equality atoms :   47 ( 104 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
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

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v5_relat_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ),
    inference(demod,[status(thm)],['28','31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','37'])).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) )
      | ( zip_tseitin_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('44',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('46',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('49',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['7','46','47','48'])).

thf('50',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ X35 )
       != sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) )
 != sk_C_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('53',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('54',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('58',plain,
    ( sk_C_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    sk_C_1 != sk_C_1 ),
    inference(demod,[status(thm)],['51','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DJttm3WLQj
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:09:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 126 iterations in 0.173s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.63  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.44/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.63  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.44/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.63  thf(t17_funct_2, conjecture,
% 0.44/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.63       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.44/0.63            ( ![E:$i]:
% 0.44/0.63              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.63            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.63          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.44/0.63               ( ![E:$i]:
% 0.44/0.63                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.44/0.63                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.44/0.63  thf('0', plain,
% 0.44/0.63      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.63         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.44/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.44/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.44/0.63  thf('3', plain,
% 0.44/0.63      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.44/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.63  thf('4', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.44/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.63  thf(d5_funct_1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.44/0.63           ( ![C:$i]:
% 0.44/0.63             ( ( r2_hidden @ C @ B ) <=>
% 0.44/0.63               ( ?[D:$i]:
% 0.44/0.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.44/0.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf('5', plain,
% 0.44/0.63      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.44/0.63         (((X11) != (k2_relat_1 @ X9))
% 0.44/0.63          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9))
% 0.44/0.63          | ~ (r2_hidden @ X12 @ X11)
% 0.44/0.63          | ~ (v1_funct_1 @ X9)
% 0.44/0.63          | ~ (v1_relat_1 @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.63  thf('6', plain,
% 0.44/0.63      (![X9 : $i, X12 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X9)
% 0.44/0.63          | ~ (v1_funct_1 @ X9)
% 0.44/0.63          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.44/0.63          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['5'])).
% 0.44/0.63  thf('7', plain,
% 0.44/0.63      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.44/0.63        | ~ (v1_funct_1 @ sk_D_2)
% 0.44/0.63        | ~ (v1_relat_1 @ sk_D_2))),
% 0.44/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.44/0.63  thf('8', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.44/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.63  thf(d1_funct_2, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_1, axiom,
% 0.44/0.63    (![B:$i,A:$i]:
% 0.44/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.63  thf('9', plain,
% 0.44/0.63      (![X27 : $i, X28 : $i]:
% 0.44/0.63         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.63  thf('10', plain,
% 0.44/0.63      (![X27 : $i, X28 : $i]:
% 0.44/0.63         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.63  thf('11', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.63         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 0.44/0.63      inference('sup+', [status(thm)], ['9', '10'])).
% 0.44/0.63  thf('12', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.63  thf(zf_stmt_3, axiom,
% 0.44/0.63    (![C:$i,B:$i,A:$i]:
% 0.44/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.63  thf(zf_stmt_5, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.63  thf('13', plain,
% 0.44/0.63      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.44/0.63         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.44/0.63          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.44/0.63          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.63  thf('14', plain,
% 0.44/0.63      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.44/0.63        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.63  thf('15', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((zip_tseitin_0 @ X1 @ X0)
% 0.44/0.63          | ((sk_B) = (X1))
% 0.44/0.63          | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['11', '14'])).
% 0.44/0.63  thf('16', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('17', plain,
% 0.44/0.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.63         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.44/0.63          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.44/0.63          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.63  thf('18', plain,
% 0.44/0.63      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.44/0.63        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.63  thf('19', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.63  thf('20', plain,
% 0.44/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.63         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.44/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.44/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.63  thf('21', plain,
% 0.44/0.63      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.44/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.63  thf('22', plain,
% 0.44/0.63      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.44/0.63        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.44/0.63      inference('demod', [status(thm)], ['18', '21'])).
% 0.44/0.63  thf('23', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((sk_B) = (X0))
% 0.44/0.63          | (zip_tseitin_0 @ X0 @ X1)
% 0.44/0.63          | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['15', '22'])).
% 0.44/0.63  thf('24', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(cc2_relset_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.63  thf('25', plain,
% 0.44/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.63         ((v5_relat_1 @ X18 @ X20)
% 0.44/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.44/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.63  thf('26', plain, ((v5_relat_1 @ sk_D_2 @ sk_B)),
% 0.44/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.44/0.63  thf(d19_relat_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( v1_relat_1 @ B ) =>
% 0.44/0.63       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.44/0.63  thf('27', plain,
% 0.44/0.63      (![X6 : $i, X7 : $i]:
% 0.44/0.63         (~ (v5_relat_1 @ X6 @ X7)
% 0.44/0.63          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.44/0.63          | ~ (v1_relat_1 @ X6))),
% 0.44/0.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.44/0.63  thf('28', plain,
% 0.44/0.63      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B))),
% 0.44/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.63  thf('29', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(cc1_relset_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.63       ( v1_relat_1 @ C ) ))).
% 0.44/0.63  thf('30', plain,
% 0.44/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.63         ((v1_relat_1 @ X15)
% 0.44/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.44/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.63  thf('31', plain, ((v1_relat_1 @ sk_D_2)),
% 0.44/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.63  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B)),
% 0.44/0.63      inference('demod', [status(thm)], ['28', '31'])).
% 0.44/0.63  thf(t3_subset, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.63  thf('33', plain,
% 0.44/0.63      (![X0 : $i, X2 : $i]:
% 0.44/0.63         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.44/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.63  thf('34', plain,
% 0.44/0.63      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.44/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.44/0.63  thf(t5_subset, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.44/0.63          ( v1_xboole_0 @ C ) ) ))).
% 0.44/0.63  thf('35', plain,
% 0.44/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.44/0.63         (~ (r2_hidden @ X3 @ X4)
% 0.44/0.63          | ~ (v1_xboole_0 @ X5)
% 0.44/0.63          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t5_subset])).
% 0.44/0.63  thf('36', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.63  thf('37', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (~ (v1_xboole_0 @ X0)
% 0.44/0.63          | ((sk_A) = (k1_relat_1 @ sk_D_2))
% 0.44/0.63          | (zip_tseitin_0 @ X0 @ X2)
% 0.44/0.63          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ sk_D_2)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['23', '36'])).
% 0.44/0.63  thf('38', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         ((zip_tseitin_0 @ X1 @ X0)
% 0.44/0.63          | ((sk_A) = (k1_relat_1 @ sk_D_2))
% 0.44/0.63          | ~ (v1_xboole_0 @ X1))),
% 0.44/0.63      inference('sup-', [status(thm)], ['8', '37'])).
% 0.44/0.63  thf('39', plain,
% 0.44/0.63      (![X27 : $i, X28 : $i]:
% 0.44/0.63         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.63  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.63  thf('41', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.44/0.63      inference('sup+', [status(thm)], ['39', '40'])).
% 0.44/0.63  thf('42', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((sk_A) = (k1_relat_1 @ sk_D_2)) | (zip_tseitin_0 @ X1 @ X0))),
% 0.44/0.63      inference('clc', [status(thm)], ['38', '41'])).
% 0.44/0.63  thf('43', plain,
% 0.44/0.63      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.44/0.63        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.63  thf('44', plain,
% 0.44/0.63      ((((sk_A) = (k1_relat_1 @ sk_D_2))
% 0.44/0.63        | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.63  thf('45', plain,
% 0.44/0.63      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.44/0.63        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.44/0.63      inference('demod', [status(thm)], ['18', '21'])).
% 0.44/0.63  thf('46', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.44/0.63      inference('clc', [status(thm)], ['44', '45'])).
% 0.44/0.63  thf('47', plain, ((v1_funct_1 @ sk_D_2)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('48', plain, ((v1_relat_1 @ sk_D_2)),
% 0.44/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.63  thf('49', plain, ((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ sk_A)),
% 0.44/0.63      inference('demod', [status(thm)], ['7', '46', '47', '48'])).
% 0.44/0.63  thf('50', plain,
% 0.44/0.63      (![X35 : $i]:
% 0.44/0.63         (~ (r2_hidden @ X35 @ sk_A)
% 0.44/0.63          | ((k1_funct_1 @ sk_D_2 @ X35) != (sk_C_1)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('51', plain,
% 0.44/0.63      (((k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)) != (sk_C_1))),
% 0.44/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.63  thf('52', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.44/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.63  thf('53', plain,
% 0.44/0.63      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.44/0.63         (((X11) != (k2_relat_1 @ X9))
% 0.44/0.63          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9)))
% 0.44/0.63          | ~ (r2_hidden @ X12 @ X11)
% 0.44/0.63          | ~ (v1_funct_1 @ X9)
% 0.44/0.63          | ~ (v1_relat_1 @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.63  thf('54', plain,
% 0.44/0.63      (![X9 : $i, X12 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X9)
% 0.44/0.63          | ~ (v1_funct_1 @ X9)
% 0.44/0.63          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.44/0.63          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.44/0.63      inference('simplify', [status(thm)], ['53'])).
% 0.44/0.63  thf('55', plain,
% 0.44/0.63      ((((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))
% 0.44/0.63        | ~ (v1_funct_1 @ sk_D_2)
% 0.44/0.63        | ~ (v1_relat_1 @ sk_D_2))),
% 0.44/0.63      inference('sup-', [status(thm)], ['52', '54'])).
% 0.44/0.63  thf('56', plain, ((v1_funct_1 @ sk_D_2)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('57', plain, ((v1_relat_1 @ sk_D_2)),
% 0.44/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.63  thf('58', plain,
% 0.44/0.63      (((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))),
% 0.44/0.63      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.44/0.63  thf('59', plain, (((sk_C_1) != (sk_C_1))),
% 0.44/0.63      inference('demod', [status(thm)], ['51', '58'])).
% 0.44/0.63  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.44/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
