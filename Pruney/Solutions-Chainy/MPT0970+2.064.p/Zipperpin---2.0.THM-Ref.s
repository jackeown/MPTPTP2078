%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LKyCPBAPJA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:25 EST 2020

% Result     : Theorem 28.55s
% Output     : Refutation 28.55s
% Verified   : 
% Statistics : Number of formulae       :  124 (1007 expanded)
%              Number of leaves         :   41 ( 304 expanded)
%              Depth                    :   19
%              Number of atoms          :  997 (14661 expanded)
%              Number of equality atoms :   72 ( 942 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X15 @ X16 ) @ X15 )
      | ( ( sk_C_1 @ X15 @ X16 )
        = ( k1_funct_1 @ X16 @ ( sk_D @ X15 @ X16 ) ) )
      | ( X15
        = ( k2_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X15 @ X16 ) @ X15 )
      | ( r2_hidden @ ( sk_D @ X15 @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ( X15
        = ( k2_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X16: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X21 ) @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('30',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['27','30'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('33',plain,(
    ~ ( r1_tarski @ sk_B @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

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

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['27','30'])).

thf('48',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_B )
      | ( X41
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_C_1 @ sk_B @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['27','30'])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X15 @ X16 ) @ X15 )
      | ( ( sk_C_1 @ X15 @ X16 )
       != ( k1_funct_1 @ X16 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X16 ) )
      | ( X15
        = ( k2_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['22','23'])).

thf('54',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_C_2 )
     != ( sk_C_1 @ sk_B @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','59'])).

thf('61',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['27','30'])).

thf('62',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X41 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','63'])).

thf('66',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['33','64','65'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( X13 = k1_xboole_0 )
      | ( X13
       != ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k1_funct_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('70',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_C_1 @ sk_B @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('72',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['22','23'])).

thf('74',plain,
    ( ( sk_C_1 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','63'])).

thf('76',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['66','76','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LKyCPBAPJA
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 28.55/28.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 28.55/28.82  % Solved by: fo/fo7.sh
% 28.55/28.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 28.55/28.82  % done 5591 iterations in 28.362s
% 28.55/28.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 28.55/28.82  % SZS output start Refutation
% 28.55/28.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 28.55/28.82  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 28.55/28.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 28.55/28.82  thf(sk_C_2_type, type, sk_C_2: $i).
% 28.55/28.82  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 28.55/28.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 28.55/28.82  thf(sk_E_type, type, sk_E: $i > $i).
% 28.55/28.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 28.55/28.82  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 28.55/28.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 28.55/28.82  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 28.55/28.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 28.55/28.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 28.55/28.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 28.55/28.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 28.55/28.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 28.55/28.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 28.55/28.82  thf(sk_A_type, type, sk_A: $i).
% 28.55/28.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 28.55/28.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 28.55/28.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 28.55/28.82  thf(sk_B_type, type, sk_B: $i).
% 28.55/28.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 28.55/28.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 28.55/28.82  thf(d5_funct_1, axiom,
% 28.55/28.82    (![A:$i]:
% 28.55/28.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 28.55/28.82       ( ![B:$i]:
% 28.55/28.82         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 28.55/28.82           ( ![C:$i]:
% 28.55/28.82             ( ( r2_hidden @ C @ B ) <=>
% 28.55/28.82               ( ?[D:$i]:
% 28.55/28.82                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 28.55/28.82                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 28.55/28.82  thf('0', plain,
% 28.55/28.82      (![X15 : $i, X16 : $i]:
% 28.55/28.82         ((r2_hidden @ (sk_C_1 @ X15 @ X16) @ X15)
% 28.55/28.82          | ((sk_C_1 @ X15 @ X16) = (k1_funct_1 @ X16 @ (sk_D @ X15 @ X16)))
% 28.55/28.82          | ((X15) = (k2_relat_1 @ X16))
% 28.55/28.82          | ~ (v1_funct_1 @ X16)
% 28.55/28.82          | ~ (v1_relat_1 @ X16))),
% 28.55/28.82      inference('cnf', [status(esa)], [d5_funct_1])).
% 28.55/28.82  thf('1', plain,
% 28.55/28.82      (![X15 : $i, X16 : $i]:
% 28.55/28.82         ((r2_hidden @ (sk_C_1 @ X15 @ X16) @ X15)
% 28.55/28.82          | (r2_hidden @ (sk_D @ X15 @ X16) @ (k1_relat_1 @ X16))
% 28.55/28.82          | ((X15) = (k2_relat_1 @ X16))
% 28.55/28.82          | ~ (v1_funct_1 @ X16)
% 28.55/28.82          | ~ (v1_relat_1 @ X16))),
% 28.55/28.82      inference('cnf', [status(esa)], [d5_funct_1])).
% 28.55/28.82  thf('2', plain,
% 28.55/28.82      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 28.55/28.82         (((X18) != (k2_relat_1 @ X16))
% 28.55/28.82          | (r2_hidden @ X20 @ X18)
% 28.55/28.82          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 28.55/28.82          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 28.55/28.82          | ~ (v1_funct_1 @ X16)
% 28.55/28.82          | ~ (v1_relat_1 @ X16))),
% 28.55/28.82      inference('cnf', [status(esa)], [d5_funct_1])).
% 28.55/28.82  thf('3', plain,
% 28.55/28.82      (![X16 : $i, X21 : $i]:
% 28.55/28.82         (~ (v1_relat_1 @ X16)
% 28.55/28.82          | ~ (v1_funct_1 @ X16)
% 28.55/28.82          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 28.55/28.82          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 28.55/28.82      inference('simplify', [status(thm)], ['2'])).
% 28.55/28.82  thf('4', plain,
% 28.55/28.82      (![X0 : $i, X1 : $i]:
% 28.55/28.82         (~ (v1_relat_1 @ X0)
% 28.55/28.82          | ~ (v1_funct_1 @ X0)
% 28.55/28.82          | ((X1) = (k2_relat_1 @ X0))
% 28.55/28.82          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 28.55/28.82          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 28.55/28.82             (k2_relat_1 @ X0))
% 28.55/28.82          | ~ (v1_funct_1 @ X0)
% 28.55/28.82          | ~ (v1_relat_1 @ X0))),
% 28.55/28.82      inference('sup-', [status(thm)], ['1', '3'])).
% 28.55/28.82  thf('5', plain,
% 28.55/28.82      (![X0 : $i, X1 : $i]:
% 28.55/28.82         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 28.55/28.82          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 28.55/28.82          | ((X1) = (k2_relat_1 @ X0))
% 28.55/28.82          | ~ (v1_funct_1 @ X0)
% 28.55/28.82          | ~ (v1_relat_1 @ X0))),
% 28.55/28.82      inference('simplify', [status(thm)], ['4'])).
% 28.55/28.82  thf('6', plain,
% 28.55/28.82      (![X0 : $i, X1 : $i]:
% 28.55/28.82         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 28.55/28.82          | ~ (v1_relat_1 @ X0)
% 28.55/28.82          | ~ (v1_funct_1 @ X0)
% 28.55/28.82          | ((X1) = (k2_relat_1 @ X0))
% 28.55/28.82          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 28.55/28.82          | ~ (v1_relat_1 @ X0)
% 28.55/28.82          | ~ (v1_funct_1 @ X0)
% 28.55/28.82          | ((X1) = (k2_relat_1 @ X0))
% 28.55/28.82          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 28.55/28.82      inference('sup+', [status(thm)], ['0', '5'])).
% 28.55/28.82  thf('7', plain,
% 28.55/28.82      (![X0 : $i, X1 : $i]:
% 28.55/28.82         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 28.55/28.82          | ((X1) = (k2_relat_1 @ X0))
% 28.55/28.82          | ~ (v1_funct_1 @ X0)
% 28.55/28.82          | ~ (v1_relat_1 @ X0)
% 28.55/28.82          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 28.55/28.82      inference('simplify', [status(thm)], ['6'])).
% 28.55/28.82  thf(t16_funct_2, conjecture,
% 28.55/28.82    (![A:$i,B:$i,C:$i]:
% 28.55/28.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 28.55/28.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 28.55/28.82       ( ( ![D:$i]:
% 28.55/28.82           ( ~( ( r2_hidden @ D @ B ) & 
% 28.55/28.82                ( ![E:$i]:
% 28.55/28.82                  ( ~( ( r2_hidden @ E @ A ) & 
% 28.55/28.82                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 28.55/28.82         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 28.55/28.82  thf(zf_stmt_0, negated_conjecture,
% 28.55/28.82    (~( ![A:$i,B:$i,C:$i]:
% 28.55/28.82        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 28.55/28.82            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 28.55/28.82          ( ( ![D:$i]:
% 28.55/28.82              ( ~( ( r2_hidden @ D @ B ) & 
% 28.55/28.82                   ( ![E:$i]:
% 28.55/28.82                     ( ~( ( r2_hidden @ E @ A ) & 
% 28.55/28.82                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 28.55/28.82            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 28.55/28.82    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 28.55/28.82  thf('8', plain,
% 28.55/28.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf(dt_k2_relset_1, axiom,
% 28.55/28.82    (![A:$i,B:$i,C:$i]:
% 28.55/28.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.55/28.82       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 28.55/28.82  thf('9', plain,
% 28.55/28.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 28.55/28.82         ((m1_subset_1 @ (k2_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X25))
% 28.55/28.82          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 28.55/28.82      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 28.55/28.82  thf('10', plain,
% 28.55/28.82      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 28.55/28.82        (k1_zfmisc_1 @ sk_B))),
% 28.55/28.82      inference('sup-', [status(thm)], ['8', '9'])).
% 28.55/28.82  thf('11', plain,
% 28.55/28.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf(redefinition_k2_relset_1, axiom,
% 28.55/28.82    (![A:$i,B:$i,C:$i]:
% 28.55/28.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.55/28.82       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 28.55/28.82  thf('12', plain,
% 28.55/28.82      (![X30 : $i, X31 : $i, X32 : $i]:
% 28.55/28.82         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 28.55/28.82          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 28.55/28.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 28.55/28.82  thf('13', plain,
% 28.55/28.82      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 28.55/28.82      inference('sup-', [status(thm)], ['11', '12'])).
% 28.55/28.82  thf('14', plain,
% 28.55/28.82      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 28.55/28.82      inference('demod', [status(thm)], ['10', '13'])).
% 28.55/28.82  thf(t3_subset, axiom,
% 28.55/28.82    (![A:$i,B:$i]:
% 28.55/28.82     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 28.55/28.82  thf('15', plain,
% 28.55/28.82      (![X4 : $i, X5 : $i]:
% 28.55/28.82         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 28.55/28.82      inference('cnf', [status(esa)], [t3_subset])).
% 28.55/28.82  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 28.55/28.82      inference('sup-', [status(thm)], ['14', '15'])).
% 28.55/28.82  thf(d3_tarski, axiom,
% 28.55/28.82    (![A:$i,B:$i]:
% 28.55/28.82     ( ( r1_tarski @ A @ B ) <=>
% 28.55/28.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 28.55/28.82  thf('17', plain,
% 28.55/28.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.55/28.82         (~ (r2_hidden @ X0 @ X1)
% 28.55/28.82          | (r2_hidden @ X0 @ X2)
% 28.55/28.82          | ~ (r1_tarski @ X1 @ X2))),
% 28.55/28.82      inference('cnf', [status(esa)], [d3_tarski])).
% 28.55/28.82  thf('18', plain,
% 28.55/28.82      (![X0 : $i]:
% 28.55/28.82         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 28.55/28.82      inference('sup-', [status(thm)], ['16', '17'])).
% 28.55/28.82  thf('19', plain,
% 28.55/28.82      (![X0 : $i]:
% 28.55/28.82         (~ (v1_relat_1 @ sk_C_2)
% 28.55/28.82          | ~ (v1_funct_1 @ sk_C_2)
% 28.55/28.82          | ((X0) = (k2_relat_1 @ sk_C_2))
% 28.55/28.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 28.55/28.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 28.55/28.82      inference('sup-', [status(thm)], ['7', '18'])).
% 28.55/28.82  thf('20', plain,
% 28.55/28.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf(cc2_relat_1, axiom,
% 28.55/28.82    (![A:$i]:
% 28.55/28.82     ( ( v1_relat_1 @ A ) =>
% 28.55/28.82       ( ![B:$i]:
% 28.55/28.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 28.55/28.82  thf('21', plain,
% 28.55/28.82      (![X7 : $i, X8 : $i]:
% 28.55/28.82         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 28.55/28.82          | (v1_relat_1 @ X7)
% 28.55/28.82          | ~ (v1_relat_1 @ X8))),
% 28.55/28.82      inference('cnf', [status(esa)], [cc2_relat_1])).
% 28.55/28.82  thf('22', plain,
% 28.55/28.82      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 28.55/28.82      inference('sup-', [status(thm)], ['20', '21'])).
% 28.55/28.82  thf(fc6_relat_1, axiom,
% 28.55/28.82    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 28.55/28.82  thf('23', plain,
% 28.55/28.82      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 28.55/28.82      inference('cnf', [status(esa)], [fc6_relat_1])).
% 28.55/28.82  thf('24', plain, ((v1_relat_1 @ sk_C_2)),
% 28.55/28.82      inference('demod', [status(thm)], ['22', '23'])).
% 28.55/28.82  thf('25', plain, ((v1_funct_1 @ sk_C_2)),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf('26', plain,
% 28.55/28.82      (![X0 : $i]:
% 28.55/28.82         (((X0) = (k2_relat_1 @ sk_C_2))
% 28.55/28.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 28.55/28.82          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 28.55/28.82      inference('demod', [status(thm)], ['19', '24', '25'])).
% 28.55/28.82  thf('27', plain,
% 28.55/28.82      (((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 28.55/28.82        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 28.55/28.82      inference('eq_fact', [status(thm)], ['26'])).
% 28.55/28.82  thf('28', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf('29', plain,
% 28.55/28.82      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 28.55/28.82      inference('sup-', [status(thm)], ['11', '12'])).
% 28.55/28.82  thf('30', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 28.55/28.82      inference('demod', [status(thm)], ['28', '29'])).
% 28.55/28.82  thf('31', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 28.55/28.82      inference('simplify_reflect-', [status(thm)], ['27', '30'])).
% 28.55/28.82  thf(t7_ordinal1, axiom,
% 28.55/28.82    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 28.55/28.82  thf('32', plain,
% 28.55/28.82      (![X22 : $i, X23 : $i]:
% 28.55/28.82         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 28.55/28.82      inference('cnf', [status(esa)], [t7_ordinal1])).
% 28.55/28.82  thf('33', plain, (~ (r1_tarski @ sk_B @ (sk_C_1 @ sk_B @ sk_C_2))),
% 28.55/28.82      inference('sup-', [status(thm)], ['31', '32'])).
% 28.55/28.82  thf(d1_funct_2, axiom,
% 28.55/28.82    (![A:$i,B:$i,C:$i]:
% 28.55/28.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.55/28.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 28.55/28.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 28.55/28.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 28.55/28.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 28.55/28.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 28.55/28.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 28.55/28.82  thf(zf_stmt_1, axiom,
% 28.55/28.82    (![B:$i,A:$i]:
% 28.55/28.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 28.55/28.82       ( zip_tseitin_0 @ B @ A ) ))).
% 28.55/28.82  thf('34', plain,
% 28.55/28.82      (![X33 : $i, X34 : $i]:
% 28.55/28.82         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 28.55/28.82  thf('35', plain,
% 28.55/28.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 28.55/28.82  thf(zf_stmt_3, axiom,
% 28.55/28.82    (![C:$i,B:$i,A:$i]:
% 28.55/28.82     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 28.55/28.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 28.55/28.82  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 28.55/28.82  thf(zf_stmt_5, axiom,
% 28.55/28.82    (![A:$i,B:$i,C:$i]:
% 28.55/28.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.55/28.82       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 28.55/28.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 28.55/28.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 28.55/28.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 28.55/28.82  thf('36', plain,
% 28.55/28.82      (![X38 : $i, X39 : $i, X40 : $i]:
% 28.55/28.82         (~ (zip_tseitin_0 @ X38 @ X39)
% 28.55/28.82          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 28.55/28.82          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 28.55/28.82  thf('37', plain,
% 28.55/28.82      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 28.55/28.82        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 28.55/28.82      inference('sup-', [status(thm)], ['35', '36'])).
% 28.55/28.82  thf('38', plain,
% 28.55/28.82      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 28.55/28.82      inference('sup-', [status(thm)], ['34', '37'])).
% 28.55/28.82  thf('39', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf('40', plain,
% 28.55/28.82      (![X35 : $i, X36 : $i, X37 : $i]:
% 28.55/28.82         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 28.55/28.82          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 28.55/28.82          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 28.55/28.82  thf('41', plain,
% 28.55/28.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 28.55/28.82        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 28.55/28.82      inference('sup-', [status(thm)], ['39', '40'])).
% 28.55/28.82  thf('42', plain,
% 28.55/28.82      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf(redefinition_k1_relset_1, axiom,
% 28.55/28.82    (![A:$i,B:$i,C:$i]:
% 28.55/28.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.55/28.82       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 28.55/28.82  thf('43', plain,
% 28.55/28.82      (![X27 : $i, X28 : $i, X29 : $i]:
% 28.55/28.82         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 28.55/28.82          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 28.55/28.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 28.55/28.82  thf('44', plain,
% 28.55/28.82      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 28.55/28.82      inference('sup-', [status(thm)], ['42', '43'])).
% 28.55/28.82  thf('45', plain,
% 28.55/28.82      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 28.55/28.82        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 28.55/28.82      inference('demod', [status(thm)], ['41', '44'])).
% 28.55/28.82  thf('46', plain,
% 28.55/28.82      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 28.55/28.82      inference('sup-', [status(thm)], ['38', '45'])).
% 28.55/28.82  thf('47', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 28.55/28.82      inference('simplify_reflect-', [status(thm)], ['27', '30'])).
% 28.55/28.82  thf('48', plain,
% 28.55/28.82      (![X41 : $i]:
% 28.55/28.82         (~ (r2_hidden @ X41 @ sk_B)
% 28.55/28.82          | ((X41) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X41))))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf('49', plain,
% 28.55/28.82      (((sk_C_1 @ sk_B @ sk_C_2)
% 28.55/28.82         = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2))))),
% 28.55/28.82      inference('sup-', [status(thm)], ['47', '48'])).
% 28.55/28.82  thf('50', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 28.55/28.82      inference('simplify_reflect-', [status(thm)], ['27', '30'])).
% 28.55/28.82  thf('51', plain,
% 28.55/28.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 28.55/28.82         (~ (r2_hidden @ (sk_C_1 @ X15 @ X16) @ X15)
% 28.55/28.82          | ((sk_C_1 @ X15 @ X16) != (k1_funct_1 @ X16 @ X17))
% 28.55/28.82          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X16))
% 28.55/28.82          | ((X15) = (k2_relat_1 @ X16))
% 28.55/28.82          | ~ (v1_funct_1 @ X16)
% 28.55/28.82          | ~ (v1_relat_1 @ X16))),
% 28.55/28.82      inference('cnf', [status(esa)], [d5_funct_1])).
% 28.55/28.82  thf('52', plain,
% 28.55/28.82      (![X0 : $i]:
% 28.55/28.82         (~ (v1_relat_1 @ sk_C_2)
% 28.55/28.82          | ~ (v1_funct_1 @ sk_C_2)
% 28.55/28.82          | ((sk_B) = (k2_relat_1 @ sk_C_2))
% 28.55/28.82          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 28.55/28.82          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 28.55/28.82      inference('sup-', [status(thm)], ['50', '51'])).
% 28.55/28.82  thf('53', plain, ((v1_relat_1 @ sk_C_2)),
% 28.55/28.82      inference('demod', [status(thm)], ['22', '23'])).
% 28.55/28.82  thf('54', plain, ((v1_funct_1 @ sk_C_2)),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf('55', plain,
% 28.55/28.82      (![X0 : $i]:
% 28.55/28.82         (((sk_B) = (k2_relat_1 @ sk_C_2))
% 28.55/28.82          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 28.55/28.82          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 28.55/28.82      inference('demod', [status(thm)], ['52', '53', '54'])).
% 28.55/28.82  thf('56', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 28.55/28.82      inference('demod', [status(thm)], ['28', '29'])).
% 28.55/28.82  thf('57', plain,
% 28.55/28.82      (![X0 : $i]:
% 28.55/28.82         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 28.55/28.82          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 28.55/28.82      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 28.55/28.82  thf('58', plain,
% 28.55/28.82      ((((sk_C_1 @ sk_B @ sk_C_2) != (sk_C_1 @ sk_B @ sk_C_2))
% 28.55/28.82        | ~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ 
% 28.55/28.82             (k1_relat_1 @ sk_C_2)))),
% 28.55/28.82      inference('sup-', [status(thm)], ['49', '57'])).
% 28.55/28.82  thf('59', plain,
% 28.55/28.82      (~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ (k1_relat_1 @ sk_C_2))),
% 28.55/28.82      inference('simplify', [status(thm)], ['58'])).
% 28.55/28.82  thf('60', plain,
% 28.55/28.82      ((~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A)
% 28.55/28.82        | ((sk_B) = (k1_xboole_0)))),
% 28.55/28.82      inference('sup-', [status(thm)], ['46', '59'])).
% 28.55/28.82  thf('61', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 28.55/28.82      inference('simplify_reflect-', [status(thm)], ['27', '30'])).
% 28.55/28.82  thf('62', plain,
% 28.55/28.82      (![X41 : $i]:
% 28.55/28.82         (~ (r2_hidden @ X41 @ sk_B) | (r2_hidden @ (sk_E @ X41) @ sk_A))),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf('63', plain, ((r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A)),
% 28.55/28.82      inference('sup-', [status(thm)], ['61', '62'])).
% 28.55/28.82  thf('64', plain, (((sk_B) = (k1_xboole_0))),
% 28.55/28.82      inference('demod', [status(thm)], ['60', '63'])).
% 28.55/28.82  thf('65', plain, (((sk_B) = (k1_xboole_0))),
% 28.55/28.82      inference('demod', [status(thm)], ['60', '63'])).
% 28.55/28.82  thf('66', plain,
% 28.55/28.82      (~ (r1_tarski @ k1_xboole_0 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2))),
% 28.55/28.82      inference('demod', [status(thm)], ['33', '64', '65'])).
% 28.55/28.82  thf(d4_funct_1, axiom,
% 28.55/28.82    (![A:$i]:
% 28.55/28.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 28.55/28.82       ( ![B:$i,C:$i]:
% 28.55/28.82         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 28.55/28.82             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 28.55/28.82               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 28.55/28.82           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 28.55/28.82             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 28.55/28.82               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 28.55/28.82  thf('67', plain,
% 28.55/28.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 28.55/28.82         ((r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 28.55/28.82          | ((X13) = (k1_xboole_0))
% 28.55/28.82          | ((X13) != (k1_funct_1 @ X12 @ X11))
% 28.55/28.82          | ~ (v1_funct_1 @ X12)
% 28.55/28.82          | ~ (v1_relat_1 @ X12))),
% 28.55/28.82      inference('cnf', [status(esa)], [d4_funct_1])).
% 28.55/28.82  thf('68', plain,
% 28.55/28.82      (![X11 : $i, X12 : $i]:
% 28.55/28.82         (~ (v1_relat_1 @ X12)
% 28.55/28.82          | ~ (v1_funct_1 @ X12)
% 28.55/28.82          | ((k1_funct_1 @ X12 @ X11) = (k1_xboole_0))
% 28.55/28.82          | (r2_hidden @ X11 @ (k1_relat_1 @ X12)))),
% 28.55/28.82      inference('simplify', [status(thm)], ['67'])).
% 28.55/28.82  thf('69', plain,
% 28.55/28.82      (~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ (k1_relat_1 @ sk_C_2))),
% 28.55/28.82      inference('simplify', [status(thm)], ['58'])).
% 28.55/28.82  thf('70', plain,
% 28.55/28.82      ((((k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)))
% 28.55/28.82          = (k1_xboole_0))
% 28.55/28.82        | ~ (v1_funct_1 @ sk_C_2)
% 28.55/28.82        | ~ (v1_relat_1 @ sk_C_2))),
% 28.55/28.82      inference('sup-', [status(thm)], ['68', '69'])).
% 28.55/28.82  thf('71', plain,
% 28.55/28.82      (((sk_C_1 @ sk_B @ sk_C_2)
% 28.55/28.82         = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2))))),
% 28.55/28.82      inference('sup-', [status(thm)], ['47', '48'])).
% 28.55/28.82  thf('72', plain, ((v1_funct_1 @ sk_C_2)),
% 28.55/28.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.55/28.82  thf('73', plain, ((v1_relat_1 @ sk_C_2)),
% 28.55/28.82      inference('demod', [status(thm)], ['22', '23'])).
% 28.55/28.82  thf('74', plain, (((sk_C_1 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 28.55/28.82      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 28.55/28.82  thf('75', plain, (((sk_B) = (k1_xboole_0))),
% 28.55/28.82      inference('demod', [status(thm)], ['60', '63'])).
% 28.55/28.82  thf('76', plain, (((sk_C_1 @ k1_xboole_0 @ sk_C_2) = (k1_xboole_0))),
% 28.55/28.82      inference('demod', [status(thm)], ['74', '75'])).
% 28.55/28.82  thf('77', plain,
% 28.55/28.82      (![X1 : $i, X3 : $i]:
% 28.55/28.82         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 28.55/28.82      inference('cnf', [status(esa)], [d3_tarski])).
% 28.55/28.82  thf('78', plain,
% 28.55/28.82      (![X1 : $i, X3 : $i]:
% 28.55/28.82         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 28.55/28.82      inference('cnf', [status(esa)], [d3_tarski])).
% 28.55/28.82  thf('79', plain,
% 28.55/28.82      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 28.55/28.82      inference('sup-', [status(thm)], ['77', '78'])).
% 28.55/28.82  thf('80', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 28.55/28.82      inference('simplify', [status(thm)], ['79'])).
% 28.55/28.82  thf('81', plain, ($false),
% 28.55/28.82      inference('demod', [status(thm)], ['66', '76', '80'])).
% 28.55/28.82  
% 28.55/28.82  % SZS output end Refutation
% 28.55/28.82  
% 28.65/28.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
