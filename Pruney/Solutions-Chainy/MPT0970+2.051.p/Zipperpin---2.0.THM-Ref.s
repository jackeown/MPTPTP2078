%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5JhaivGbxW

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:24 EST 2020

% Result     : Theorem 3.20s
% Output     : Refutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 341 expanded)
%              Number of leaves         :   41 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  945 (4395 expanded)
%              Number of equality atoms :   70 ( 283 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['12','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('23',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_B )
      | ( X39
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_C_1 @ sk_B @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','30'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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

thf('46',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('47',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('56',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('59',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ sk_B ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['26','29'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('67',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['48','67'])).

thf('69',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['45','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','69'])).

thf('71',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['26','29'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_C_2 )
     != ( sk_C_1 @ sk_B @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','72'])).

thf('74',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','30'])).

thf('75',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X39 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ( sk_C_1 @ sk_B @ sk_C_2 )
 != ( sk_C_1 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    $false ),
    inference(simplify,[status(thm)],['77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5JhaivGbxW
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.20/3.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.20/3.44  % Solved by: fo/fo7.sh
% 3.20/3.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.20/3.44  % done 1356 iterations in 2.991s
% 3.20/3.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.20/3.44  % SZS output start Refutation
% 3.20/3.44  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.20/3.44  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.20/3.44  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.20/3.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.20/3.44  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.20/3.44  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.20/3.44  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.20/3.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.20/3.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.20/3.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.20/3.44  thf(sk_E_type, type, sk_E: $i > $i).
% 3.20/3.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.20/3.44  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.20/3.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.20/3.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.20/3.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.20/3.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.20/3.44  thf(sk_A_type, type, sk_A: $i).
% 3.20/3.44  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.20/3.44  thf(sk_B_type, type, sk_B: $i).
% 3.20/3.44  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 3.20/3.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.20/3.44  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.20/3.44  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.20/3.44  thf(d5_funct_1, axiom,
% 3.20/3.44    (![A:$i]:
% 3.20/3.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.20/3.44       ( ![B:$i]:
% 3.20/3.44         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 3.20/3.44           ( ![C:$i]:
% 3.20/3.44             ( ( r2_hidden @ C @ B ) <=>
% 3.20/3.44               ( ?[D:$i]:
% 3.20/3.44                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 3.20/3.44                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 3.20/3.44  thf('0', plain,
% 3.20/3.44      (![X15 : $i, X16 : $i]:
% 3.20/3.44         ((r2_hidden @ (sk_C_1 @ X15 @ X16) @ X15)
% 3.20/3.44          | ((sk_C_1 @ X15 @ X16) = (k1_funct_1 @ X16 @ (sk_D @ X15 @ X16)))
% 3.20/3.44          | ((X15) = (k2_relat_1 @ X16))
% 3.20/3.44          | ~ (v1_funct_1 @ X16)
% 3.20/3.44          | ~ (v1_relat_1 @ X16))),
% 3.20/3.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 3.20/3.44  thf('1', plain,
% 3.20/3.44      (![X15 : $i, X16 : $i]:
% 3.20/3.44         ((r2_hidden @ (sk_C_1 @ X15 @ X16) @ X15)
% 3.20/3.44          | (r2_hidden @ (sk_D @ X15 @ X16) @ (k1_relat_1 @ X16))
% 3.20/3.44          | ((X15) = (k2_relat_1 @ X16))
% 3.20/3.44          | ~ (v1_funct_1 @ X16)
% 3.20/3.44          | ~ (v1_relat_1 @ X16))),
% 3.20/3.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 3.20/3.44  thf('2', plain,
% 3.20/3.44      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 3.20/3.44         (((X18) != (k2_relat_1 @ X16))
% 3.20/3.44          | (r2_hidden @ X20 @ X18)
% 3.20/3.44          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 3.20/3.44          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 3.20/3.44          | ~ (v1_funct_1 @ X16)
% 3.20/3.44          | ~ (v1_relat_1 @ X16))),
% 3.20/3.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 3.20/3.44  thf('3', plain,
% 3.20/3.44      (![X16 : $i, X21 : $i]:
% 3.20/3.44         (~ (v1_relat_1 @ X16)
% 3.20/3.44          | ~ (v1_funct_1 @ X16)
% 3.20/3.44          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 3.20/3.44          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 3.20/3.44      inference('simplify', [status(thm)], ['2'])).
% 3.20/3.44  thf('4', plain,
% 3.20/3.44      (![X0 : $i, X1 : $i]:
% 3.20/3.44         (~ (v1_relat_1 @ X0)
% 3.20/3.44          | ~ (v1_funct_1 @ X0)
% 3.20/3.44          | ((X1) = (k2_relat_1 @ X0))
% 3.20/3.44          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 3.20/3.44          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 3.20/3.44             (k2_relat_1 @ X0))
% 3.20/3.44          | ~ (v1_funct_1 @ X0)
% 3.20/3.44          | ~ (v1_relat_1 @ X0))),
% 3.20/3.44      inference('sup-', [status(thm)], ['1', '3'])).
% 3.20/3.44  thf('5', plain,
% 3.20/3.44      (![X0 : $i, X1 : $i]:
% 3.20/3.44         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 3.20/3.44          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 3.20/3.44          | ((X1) = (k2_relat_1 @ X0))
% 3.20/3.44          | ~ (v1_funct_1 @ X0)
% 3.20/3.44          | ~ (v1_relat_1 @ X0))),
% 3.20/3.44      inference('simplify', [status(thm)], ['4'])).
% 3.20/3.44  thf('6', plain,
% 3.20/3.44      (![X0 : $i, X1 : $i]:
% 3.20/3.44         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 3.20/3.44          | ~ (v1_relat_1 @ X0)
% 3.20/3.44          | ~ (v1_funct_1 @ X0)
% 3.20/3.44          | ((X1) = (k2_relat_1 @ X0))
% 3.20/3.44          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 3.20/3.44          | ~ (v1_relat_1 @ X0)
% 3.20/3.44          | ~ (v1_funct_1 @ X0)
% 3.20/3.44          | ((X1) = (k2_relat_1 @ X0))
% 3.20/3.44          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 3.20/3.44      inference('sup+', [status(thm)], ['0', '5'])).
% 3.20/3.44  thf('7', plain,
% 3.20/3.44      (![X0 : $i, X1 : $i]:
% 3.20/3.44         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 3.20/3.44          | ((X1) = (k2_relat_1 @ X0))
% 3.20/3.44          | ~ (v1_funct_1 @ X0)
% 3.20/3.44          | ~ (v1_relat_1 @ X0)
% 3.20/3.44          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.20/3.44      inference('simplify', [status(thm)], ['6'])).
% 3.20/3.44  thf(t16_funct_2, conjecture,
% 3.20/3.44    (![A:$i,B:$i,C:$i]:
% 3.20/3.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.20/3.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.20/3.44       ( ( ![D:$i]:
% 3.20/3.44           ( ~( ( r2_hidden @ D @ B ) & 
% 3.20/3.44                ( ![E:$i]:
% 3.20/3.44                  ( ~( ( r2_hidden @ E @ A ) & 
% 3.20/3.44                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 3.20/3.44         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 3.20/3.44  thf(zf_stmt_0, negated_conjecture,
% 3.20/3.44    (~( ![A:$i,B:$i,C:$i]:
% 3.20/3.44        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.20/3.44            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.20/3.44          ( ( ![D:$i]:
% 3.20/3.44              ( ~( ( r2_hidden @ D @ B ) & 
% 3.20/3.44                   ( ![E:$i]:
% 3.20/3.44                     ( ~( ( r2_hidden @ E @ A ) & 
% 3.20/3.44                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 3.20/3.44            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 3.20/3.44    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 3.20/3.44  thf('8', plain,
% 3.20/3.44      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.44  thf(cc2_relset_1, axiom,
% 3.20/3.44    (![A:$i,B:$i,C:$i]:
% 3.20/3.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.20/3.44       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.20/3.44  thf('9', plain,
% 3.20/3.44      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.20/3.44         ((v5_relat_1 @ X22 @ X24)
% 3.20/3.44          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.20/3.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.20/3.44  thf('10', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 3.20/3.44      inference('sup-', [status(thm)], ['8', '9'])).
% 3.20/3.44  thf(d19_relat_1, axiom,
% 3.20/3.44    (![A:$i,B:$i]:
% 3.20/3.44     ( ( v1_relat_1 @ B ) =>
% 3.20/3.44       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.20/3.44  thf('11', plain,
% 3.20/3.44      (![X11 : $i, X12 : $i]:
% 3.20/3.44         (~ (v5_relat_1 @ X11 @ X12)
% 3.20/3.44          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 3.20/3.44          | ~ (v1_relat_1 @ X11))),
% 3.20/3.44      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.20/3.44  thf('12', plain,
% 3.20/3.44      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 3.20/3.44      inference('sup-', [status(thm)], ['10', '11'])).
% 3.20/3.44  thf('13', plain,
% 3.20/3.44      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.44  thf(cc2_relat_1, axiom,
% 3.20/3.44    (![A:$i]:
% 3.20/3.44     ( ( v1_relat_1 @ A ) =>
% 3.20/3.44       ( ![B:$i]:
% 3.20/3.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.20/3.44  thf('14', plain,
% 3.20/3.44      (![X9 : $i, X10 : $i]:
% 3.20/3.44         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 3.20/3.44          | (v1_relat_1 @ X9)
% 3.20/3.44          | ~ (v1_relat_1 @ X10))),
% 3.20/3.44      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.20/3.44  thf('15', plain,
% 3.20/3.44      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 3.20/3.44      inference('sup-', [status(thm)], ['13', '14'])).
% 3.20/3.44  thf(fc6_relat_1, axiom,
% 3.20/3.44    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.20/3.44  thf('16', plain,
% 3.20/3.44      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 3.20/3.44      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.20/3.44  thf('17', plain, ((v1_relat_1 @ sk_C_2)),
% 3.20/3.44      inference('demod', [status(thm)], ['15', '16'])).
% 3.20/3.44  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 3.20/3.44      inference('demod', [status(thm)], ['12', '17'])).
% 3.20/3.44  thf(d3_tarski, axiom,
% 3.20/3.44    (![A:$i,B:$i]:
% 3.20/3.44     ( ( r1_tarski @ A @ B ) <=>
% 3.20/3.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.20/3.44  thf('19', plain,
% 3.20/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.20/3.44         (~ (r2_hidden @ X0 @ X1)
% 3.20/3.44          | (r2_hidden @ X0 @ X2)
% 3.20/3.44          | ~ (r1_tarski @ X1 @ X2))),
% 3.20/3.44      inference('cnf', [status(esa)], [d3_tarski])).
% 3.20/3.44  thf('20', plain,
% 3.20/3.44      (![X0 : $i]:
% 3.20/3.44         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 3.20/3.44      inference('sup-', [status(thm)], ['18', '19'])).
% 3.20/3.44  thf('21', plain,
% 3.20/3.44      (![X0 : $i]:
% 3.20/3.44         (~ (v1_relat_1 @ sk_C_2)
% 3.20/3.44          | ~ (v1_funct_1 @ sk_C_2)
% 3.20/3.44          | ((X0) = (k2_relat_1 @ sk_C_2))
% 3.20/3.44          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 3.20/3.44          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 3.20/3.44      inference('sup-', [status(thm)], ['7', '20'])).
% 3.20/3.44  thf('22', plain, ((v1_relat_1 @ sk_C_2)),
% 3.20/3.44      inference('demod', [status(thm)], ['15', '16'])).
% 3.20/3.44  thf('23', plain, ((v1_funct_1 @ sk_C_2)),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.44  thf('24', plain,
% 3.20/3.44      (![X0 : $i]:
% 3.20/3.44         (((X0) = (k2_relat_1 @ sk_C_2))
% 3.20/3.44          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 3.20/3.44          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 3.20/3.44      inference('demod', [status(thm)], ['21', '22', '23'])).
% 3.20/3.44  thf('25', plain,
% 3.20/3.44      (((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 3.20/3.44        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 3.20/3.44      inference('eq_fact', [status(thm)], ['24'])).
% 3.20/3.44  thf('26', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.44  thf('27', plain,
% 3.20/3.44      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.44  thf(redefinition_k2_relset_1, axiom,
% 3.20/3.44    (![A:$i,B:$i,C:$i]:
% 3.20/3.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.20/3.44       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.20/3.44  thf('28', plain,
% 3.20/3.44      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.20/3.44         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 3.20/3.44          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 3.20/3.44      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.20/3.44  thf('29', plain,
% 3.20/3.44      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 3.20/3.44      inference('sup-', [status(thm)], ['27', '28'])).
% 3.20/3.44  thf('30', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 3.20/3.44      inference('demod', [status(thm)], ['26', '29'])).
% 3.20/3.44  thf('31', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 3.20/3.44      inference('simplify_reflect-', [status(thm)], ['25', '30'])).
% 3.20/3.44  thf('32', plain,
% 3.20/3.44      (![X39 : $i]:
% 3.20/3.44         (~ (r2_hidden @ X39 @ sk_B)
% 3.20/3.44          | ((X39) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X39))))),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.44  thf('33', plain,
% 3.20/3.44      (((sk_C_1 @ sk_B @ sk_C_2)
% 3.20/3.44         = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2))))),
% 3.20/3.44      inference('sup-', [status(thm)], ['31', '32'])).
% 3.20/3.44  thf('34', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 3.20/3.44      inference('simplify_reflect-', [status(thm)], ['25', '30'])).
% 3.20/3.44  thf('35', plain,
% 3.20/3.44      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.20/3.44         (~ (r2_hidden @ (sk_C_1 @ X15 @ X16) @ X15)
% 3.20/3.44          | ((sk_C_1 @ X15 @ X16) != (k1_funct_1 @ X16 @ X17))
% 3.20/3.44          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X16))
% 3.20/3.44          | ((X15) = (k2_relat_1 @ X16))
% 3.20/3.44          | ~ (v1_funct_1 @ X16)
% 3.20/3.44          | ~ (v1_relat_1 @ X16))),
% 3.20/3.44      inference('cnf', [status(esa)], [d5_funct_1])).
% 3.20/3.44  thf('36', plain,
% 3.20/3.44      (![X0 : $i]:
% 3.20/3.44         (~ (v1_relat_1 @ sk_C_2)
% 3.20/3.44          | ~ (v1_funct_1 @ sk_C_2)
% 3.20/3.44          | ((sk_B) = (k2_relat_1 @ sk_C_2))
% 3.20/3.44          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 3.20/3.44          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 3.20/3.44      inference('sup-', [status(thm)], ['34', '35'])).
% 3.20/3.44  thf('37', plain, ((v1_relat_1 @ sk_C_2)),
% 3.20/3.44      inference('demod', [status(thm)], ['15', '16'])).
% 3.20/3.44  thf('38', plain, ((v1_funct_1 @ sk_C_2)),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.44  thf('39', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.44  thf(d1_funct_2, axiom,
% 3.20/3.44    (![A:$i,B:$i,C:$i]:
% 3.20/3.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.20/3.44       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.20/3.44           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.20/3.44             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.20/3.44         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.20/3.44           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.20/3.44             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.20/3.44  thf(zf_stmt_1, axiom,
% 3.20/3.44    (![C:$i,B:$i,A:$i]:
% 3.20/3.44     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.20/3.44       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.20/3.44  thf('40', plain,
% 3.20/3.44      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.20/3.44         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 3.20/3.44          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 3.20/3.44          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.20/3.44  thf('41', plain,
% 3.20/3.44      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.20/3.44        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 3.20/3.44      inference('sup-', [status(thm)], ['39', '40'])).
% 3.20/3.44  thf('42', plain,
% 3.20/3.44      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.44  thf(redefinition_k1_relset_1, axiom,
% 3.20/3.44    (![A:$i,B:$i,C:$i]:
% 3.20/3.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.20/3.44       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.20/3.44  thf('43', plain,
% 3.20/3.44      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.20/3.44         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 3.20/3.44          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.20/3.44      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.20/3.44  thf('44', plain,
% 3.20/3.44      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.20/3.44      inference('sup-', [status(thm)], ['42', '43'])).
% 3.20/3.44  thf('45', plain,
% 3.20/3.44      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.20/3.44        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.20/3.44      inference('demod', [status(thm)], ['41', '44'])).
% 3.20/3.44  thf('46', plain,
% 3.20/3.44      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.44  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.20/3.44  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.20/3.44  thf(zf_stmt_4, axiom,
% 3.20/3.44    (![B:$i,A:$i]:
% 3.20/3.44     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.20/3.44       ( zip_tseitin_0 @ B @ A ) ))).
% 3.20/3.44  thf(zf_stmt_5, axiom,
% 3.20/3.44    (![A:$i,B:$i,C:$i]:
% 3.20/3.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.20/3.44       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.20/3.44         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.20/3.44           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.20/3.44             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.20/3.44  thf('47', plain,
% 3.20/3.44      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.20/3.44         (~ (zip_tseitin_0 @ X36 @ X37)
% 3.20/3.44          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 3.20/3.44          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 3.20/3.44      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.20/3.44  thf('48', plain,
% 3.20/3.44      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.20/3.44        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.20/3.44      inference('sup-', [status(thm)], ['46', '47'])).
% 3.20/3.44  thf('49', plain,
% 3.20/3.44      (![X0 : $i, X1 : $i]:
% 3.20/3.44         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 3.20/3.44          | ((X1) = (k2_relat_1 @ X0))
% 3.20/3.44          | ~ (v1_funct_1 @ X0)
% 3.20/3.44          | ~ (v1_relat_1 @ X0)
% 3.20/3.44          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.20/3.44      inference('simplify', [status(thm)], ['6'])).
% 3.20/3.44  thf(t113_zfmisc_1, axiom,
% 3.20/3.44    (![A:$i,B:$i]:
% 3.20/3.44     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.20/3.44       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.20/3.45  thf('50', plain,
% 3.20/3.45      (![X5 : $i, X6 : $i]:
% 3.20/3.45         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.20/3.45      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.20/3.45  thf('51', plain,
% 3.20/3.45      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.20/3.45      inference('simplify', [status(thm)], ['50'])).
% 3.20/3.45  thf(t152_zfmisc_1, axiom,
% 3.20/3.45    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 3.20/3.45  thf('52', plain,
% 3.20/3.45      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 3.20/3.45      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 3.20/3.45  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.20/3.45      inference('sup-', [status(thm)], ['51', '52'])).
% 3.20/3.45  thf('54', plain,
% 3.20/3.45      (![X0 : $i]:
% 3.20/3.45         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ (k2_relat_1 @ X0))
% 3.20/3.45          | ~ (v1_relat_1 @ X0)
% 3.20/3.45          | ~ (v1_funct_1 @ X0)
% 3.20/3.45          | ((k1_xboole_0) = (k2_relat_1 @ X0)))),
% 3.20/3.45      inference('sup-', [status(thm)], ['49', '53'])).
% 3.20/3.45  thf('55', plain,
% 3.20/3.45      (![X0 : $i]:
% 3.20/3.45         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 3.20/3.45      inference('sup-', [status(thm)], ['18', '19'])).
% 3.20/3.45  thf('56', plain,
% 3.20/3.45      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_2))
% 3.20/3.45        | ~ (v1_funct_1 @ sk_C_2)
% 3.20/3.45        | ~ (v1_relat_1 @ sk_C_2)
% 3.20/3.45        | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ sk_B))),
% 3.20/3.45      inference('sup-', [status(thm)], ['54', '55'])).
% 3.20/3.45  thf('57', plain, ((v1_funct_1 @ sk_C_2)),
% 3.20/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.45  thf('58', plain, ((v1_relat_1 @ sk_C_2)),
% 3.20/3.45      inference('demod', [status(thm)], ['15', '16'])).
% 3.20/3.45  thf('59', plain,
% 3.20/3.45      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_2))
% 3.20/3.45        | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ sk_B))),
% 3.20/3.45      inference('demod', [status(thm)], ['56', '57', '58'])).
% 3.20/3.45  thf('60', plain,
% 3.20/3.45      (![X31 : $i, X32 : $i]:
% 3.20/3.45         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 3.20/3.45      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.20/3.45  thf('61', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.20/3.45      inference('sup-', [status(thm)], ['51', '52'])).
% 3.20/3.45  thf('62', plain,
% 3.20/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.20/3.45         (~ (r2_hidden @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 3.20/3.45      inference('sup-', [status(thm)], ['60', '61'])).
% 3.20/3.45  thf('63', plain,
% 3.20/3.45      (![X0 : $i]:
% 3.20/3.45         (((k1_xboole_0) = (k2_relat_1 @ sk_C_2)) | (zip_tseitin_0 @ sk_B @ X0))),
% 3.20/3.45      inference('sup-', [status(thm)], ['59', '62'])).
% 3.20/3.45  thf('64', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 3.20/3.45      inference('demod', [status(thm)], ['26', '29'])).
% 3.20/3.45  thf('65', plain,
% 3.20/3.45      (![X0 : $i]: (((k1_xboole_0) != (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 3.20/3.45      inference('sup-', [status(thm)], ['63', '64'])).
% 3.20/3.45  thf('66', plain,
% 3.20/3.45      (![X31 : $i, X32 : $i]:
% 3.20/3.45         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 3.20/3.45      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.20/3.45  thf('67', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 3.20/3.45      inference('clc', [status(thm)], ['65', '66'])).
% 3.20/3.45  thf('68', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)),
% 3.20/3.45      inference('demod', [status(thm)], ['48', '67'])).
% 3.20/3.45  thf('69', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.20/3.45      inference('demod', [status(thm)], ['45', '68'])).
% 3.20/3.45  thf('70', plain,
% 3.20/3.45      (![X0 : $i]:
% 3.20/3.45         (((sk_B) = (k2_relat_1 @ sk_C_2))
% 3.20/3.45          | ~ (r2_hidden @ X0 @ sk_A)
% 3.20/3.45          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 3.20/3.45      inference('demod', [status(thm)], ['36', '37', '38', '69'])).
% 3.20/3.45  thf('71', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 3.20/3.45      inference('demod', [status(thm)], ['26', '29'])).
% 3.20/3.45  thf('72', plain,
% 3.20/3.45      (![X0 : $i]:
% 3.20/3.45         (~ (r2_hidden @ X0 @ sk_A)
% 3.20/3.45          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 3.20/3.45      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 3.20/3.45  thf('73', plain,
% 3.20/3.45      ((((sk_C_1 @ sk_B @ sk_C_2) != (sk_C_1 @ sk_B @ sk_C_2))
% 3.20/3.45        | ~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A))),
% 3.20/3.45      inference('sup-', [status(thm)], ['33', '72'])).
% 3.20/3.45  thf('74', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 3.20/3.45      inference('simplify_reflect-', [status(thm)], ['25', '30'])).
% 3.20/3.45  thf('75', plain,
% 3.20/3.45      (![X39 : $i]:
% 3.20/3.45         (~ (r2_hidden @ X39 @ sk_B) | (r2_hidden @ (sk_E @ X39) @ sk_A))),
% 3.20/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.20/3.45  thf('76', plain, ((r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A)),
% 3.20/3.45      inference('sup-', [status(thm)], ['74', '75'])).
% 3.20/3.45  thf('77', plain, (((sk_C_1 @ sk_B @ sk_C_2) != (sk_C_1 @ sk_B @ sk_C_2))),
% 3.20/3.45      inference('demod', [status(thm)], ['73', '76'])).
% 3.20/3.45  thf('78', plain, ($false), inference('simplify', [status(thm)], ['77'])).
% 3.20/3.45  
% 3.20/3.45  % SZS output end Refutation
% 3.20/3.45  
% 3.20/3.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
