%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wzJNYQIIRr

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:24 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 147 expanded)
%              Number of leaves         :   38 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  684 (1697 expanded)
%              Number of equality atoms :   42 ( 108 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_B )
      | ( X39
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X39 ) ) ) ) ),
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
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X39 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('36',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

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
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['23','36','39'])).

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

thf('41',plain,(
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

thf('42',plain,(
    ! [X16: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X21 ) @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['43','44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['20','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['14','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wzJNYQIIRr
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:29:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.60/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.80  % Solved by: fo/fo7.sh
% 0.60/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.80  % done 249 iterations in 0.334s
% 0.60/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.80  % SZS output start Refutation
% 0.60/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.80  thf(sk_E_type, type, sk_E: $i > $i).
% 0.60/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.60/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.80  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.60/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.80  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.60/0.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.60/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.80  thf(t16_funct_2, conjecture,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.80       ( ( ![D:$i]:
% 0.60/0.80           ( ~( ( r2_hidden @ D @ B ) & 
% 0.60/0.80                ( ![E:$i]:
% 0.60/0.80                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.60/0.80                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.60/0.80         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.60/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.80    (~( ![A:$i,B:$i,C:$i]:
% 0.60/0.80        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.80            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.80          ( ( ![D:$i]:
% 0.60/0.80              ( ~( ( r2_hidden @ D @ B ) & 
% 0.60/0.80                   ( ![E:$i]:
% 0.60/0.80                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.60/0.80                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.60/0.80            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.60/0.80    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.60/0.80  thf('0', plain,
% 0.60/0.80      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(dt_k2_relset_1, axiom,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.80       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.60/0.80  thf('1', plain,
% 0.60/0.80      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.60/0.80         ((m1_subset_1 @ (k2_relset_1 @ X22 @ X23 @ X24) @ (k1_zfmisc_1 @ X23))
% 0.60/0.80          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.60/0.80      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.60/0.80  thf('2', plain,
% 0.60/0.80      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 0.60/0.80        (k1_zfmisc_1 @ sk_B))),
% 0.60/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.60/0.80  thf('3', plain,
% 0.60/0.80      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(redefinition_k2_relset_1, axiom,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.80       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.60/0.80  thf('4', plain,
% 0.60/0.80      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.60/0.80         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.60/0.80          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.60/0.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.60/0.80  thf('5', plain,
% 0.60/0.80      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.60/0.80      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.80  thf('6', plain,
% 0.60/0.80      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['2', '5'])).
% 0.60/0.80  thf(t3_subset, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.80  thf('7', plain,
% 0.60/0.80      (![X8 : $i, X9 : $i]:
% 0.60/0.80         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.80  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.60/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.80  thf(d10_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.80  thf('9', plain,
% 0.60/0.80      (![X4 : $i, X6 : $i]:
% 0.60/0.80         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.60/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.80  thf('10', plain,
% 0.60/0.80      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.60/0.80        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['8', '9'])).
% 0.60/0.80  thf('11', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('12', plain,
% 0.60/0.80      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.60/0.80      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.80  thf('13', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.60/0.80  thf('14', plain, (~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.60/0.80      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 0.60/0.80  thf(d3_tarski, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.80  thf('15', plain,
% 0.60/0.80      (![X1 : $i, X3 : $i]:
% 0.60/0.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.80  thf('16', plain,
% 0.60/0.80      (![X39 : $i]:
% 0.60/0.80         (~ (r2_hidden @ X39 @ sk_B)
% 0.60/0.80          | ((X39) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X39))))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('17', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((r1_tarski @ sk_B @ X0)
% 0.60/0.80          | ((sk_C @ X0 @ sk_B)
% 0.60/0.80              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.60/0.80      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.80  thf('18', plain,
% 0.60/0.80      (![X1 : $i, X3 : $i]:
% 0.60/0.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.80  thf('19', plain,
% 0.60/0.80      (![X39 : $i]:
% 0.60/0.80         (~ (r2_hidden @ X39 @ sk_B) | (r2_hidden @ (sk_E @ X39) @ sk_A))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('20', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((r1_tarski @ sk_B @ X0)
% 0.60/0.80          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.60/0.80      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.80  thf('21', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(d1_funct_2, axiom,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.80       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.80           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.60/0.80             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.60/0.80         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.80           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.60/0.80             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.60/0.80  thf(zf_stmt_1, axiom,
% 0.60/0.80    (![C:$i,B:$i,A:$i]:
% 0.60/0.80     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.60/0.80       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.60/0.80  thf('22', plain,
% 0.60/0.80      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.60/0.80         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.60/0.80          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.60/0.80          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.80  thf('23', plain,
% 0.60/0.80      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.60/0.80        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['21', '22'])).
% 0.60/0.80  thf('24', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.60/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.80  thf(zf_stmt_2, axiom,
% 0.60/0.80    (![B:$i,A:$i]:
% 0.60/0.80     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.80       ( zip_tseitin_0 @ B @ A ) ))).
% 0.60/0.80  thf('25', plain,
% 0.60/0.80      (![X31 : $i, X32 : $i]:
% 0.60/0.80         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.60/0.80  thf('26', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.60/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.80  thf('27', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.80         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.60/0.80      inference('sup+', [status(thm)], ['25', '26'])).
% 0.60/0.80  thf('28', plain,
% 0.60/0.80      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.60/0.80  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.60/0.80  thf(zf_stmt_5, axiom,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.80       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.60/0.80         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.80           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.60/0.80             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.60/0.80  thf('29', plain,
% 0.60/0.80      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.60/0.80         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.60/0.80          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.60/0.80          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.80  thf('30', plain,
% 0.60/0.80      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.60/0.80        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.60/0.80      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.80  thf('31', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.60/0.80      inference('sup-', [status(thm)], ['27', '30'])).
% 0.60/0.80  thf('32', plain,
% 0.60/0.80      (![X4 : $i, X6 : $i]:
% 0.60/0.80         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.60/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.80  thf('33', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.60/0.80          | ~ (r1_tarski @ X0 @ sk_B)
% 0.60/0.80          | ((X0) = (sk_B)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.80  thf('34', plain,
% 0.60/0.80      ((((k2_relat_1 @ sk_C_2) = (sk_B))
% 0.60/0.80        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.60/0.80      inference('sup-', [status(thm)], ['24', '33'])).
% 0.60/0.80  thf('35', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.60/0.80  thf('36', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)),
% 0.60/0.80      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.60/0.80  thf('37', plain,
% 0.60/0.80      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.80  thf('38', plain,
% 0.60/0.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.80         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.60/0.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.60/0.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.80  thf('39', plain,
% 0.60/0.80      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.60/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.60/0.80  thf('40', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.60/0.80      inference('demod', [status(thm)], ['23', '36', '39'])).
% 0.60/0.80  thf(d5_funct_1, axiom,
% 0.60/0.80    (![A:$i]:
% 0.60/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.80       ( ![B:$i]:
% 0.60/0.80         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.60/0.80           ( ![C:$i]:
% 0.60/0.80             ( ( r2_hidden @ C @ B ) <=>
% 0.60/0.80               ( ?[D:$i]:
% 0.60/0.80                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.60/0.80                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.60/0.80  thf('41', plain,
% 0.60/0.80      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.60/0.80         (((X18) != (k2_relat_1 @ X16))
% 0.60/0.80          | (r2_hidden @ X20 @ X18)
% 0.60/0.80          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.60/0.80          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 0.60/0.80          | ~ (v1_funct_1 @ X16)
% 0.60/0.80          | ~ (v1_relat_1 @ X16))),
% 0.60/0.80      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.60/0.80  thf('42', plain,
% 0.60/0.80      (![X16 : $i, X21 : $i]:
% 0.60/0.80         (~ (v1_relat_1 @ X16)
% 0.60/0.80          | ~ (v1_funct_1 @ X16)
% 0.60/0.80          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.60/0.80          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 0.60/0.80      inference('simplify', [status(thm)], ['41'])).
% 0.60/0.80  thf('43', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (r2_hidden @ X0 @ sk_A)
% 0.60/0.80          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.60/0.80          | ~ (v1_funct_1 @ sk_C_2)
% 0.60/0.80          | ~ (v1_relat_1 @ sk_C_2))),
% 0.60/0.80      inference('sup-', [status(thm)], ['40', '42'])).
% 0.60/0.80  thf('44', plain, ((v1_funct_1 @ sk_C_2)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('45', plain,
% 0.60/0.80      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(cc2_relat_1, axiom,
% 0.60/0.80    (![A:$i]:
% 0.60/0.80     ( ( v1_relat_1 @ A ) =>
% 0.60/0.80       ( ![B:$i]:
% 0.60/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.60/0.80  thf('46', plain,
% 0.60/0.80      (![X11 : $i, X12 : $i]:
% 0.60/0.80         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.60/0.80          | (v1_relat_1 @ X11)
% 0.60/0.80          | ~ (v1_relat_1 @ X12))),
% 0.60/0.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.60/0.80  thf('47', plain,
% 0.60/0.80      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.60/0.80      inference('sup-', [status(thm)], ['45', '46'])).
% 0.60/0.80  thf(fc6_relat_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.60/0.80  thf('48', plain,
% 0.60/0.80      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.60/0.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.80  thf('49', plain, ((v1_relat_1 @ sk_C_2)),
% 0.60/0.80      inference('demod', [status(thm)], ['47', '48'])).
% 0.60/0.80  thf('50', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (r2_hidden @ X0 @ sk_A)
% 0.60/0.80          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.60/0.80      inference('demod', [status(thm)], ['43', '44', '49'])).
% 0.60/0.80  thf('51', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((r1_tarski @ sk_B @ X0)
% 0.60/0.80          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.60/0.80             (k2_relat_1 @ sk_C_2)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['20', '50'])).
% 0.60/0.80  thf('52', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 0.60/0.80          | (r1_tarski @ sk_B @ X0)
% 0.60/0.80          | (r1_tarski @ sk_B @ X0))),
% 0.60/0.80      inference('sup+', [status(thm)], ['17', '51'])).
% 0.60/0.80  thf('53', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         ((r1_tarski @ sk_B @ X0)
% 0.60/0.80          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 0.60/0.80      inference('simplify', [status(thm)], ['52'])).
% 0.60/0.80  thf('54', plain,
% 0.60/0.80      (![X1 : $i, X3 : $i]:
% 0.60/0.80         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.60/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.80  thf('55', plain,
% 0.60/0.80      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.60/0.80        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['53', '54'])).
% 0.60/0.80  thf('56', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.60/0.80      inference('simplify', [status(thm)], ['55'])).
% 0.60/0.80  thf('57', plain, ($false), inference('demod', [status(thm)], ['14', '56'])).
% 0.60/0.80  
% 0.60/0.80  % SZS output end Refutation
% 0.60/0.80  
% 0.60/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
