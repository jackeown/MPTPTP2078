%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IqB1XkdxSO

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:24 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 150 expanded)
%              Number of leaves         :   38 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  696 (1716 expanded)
%              Number of equality atoms :   42 ( 108 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X25 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_B )
      | ( X42
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X42 ) ) ) ) ),
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
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X42 ) @ sk_A ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
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
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('38',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['23','38','41'])).

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

thf('43',plain,(
    ! [X19: $i,X21: $i,X23: $i,X24: $i] :
      ( ( X21
       != ( k2_relat_1 @ X19 ) )
      | ( r2_hidden @ X23 @ X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X19 ) )
      | ( X23
       != ( k1_funct_1 @ X19 @ X24 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('44',plain,(
    ! [X19: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X19 @ X24 ) @ ( k2_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['45','46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['20','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['14','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IqB1XkdxSO
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:38:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 327 iterations in 0.271s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.52/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.52/0.73  thf(sk_E_type, type, sk_E: $i > $i).
% 0.52/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.52/0.73  thf(t16_funct_2, conjecture,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.73       ( ( ![D:$i]:
% 0.52/0.73           ( ~( ( r2_hidden @ D @ B ) & 
% 0.52/0.73                ( ![E:$i]:
% 0.52/0.73                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.52/0.73                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.52/0.73         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.73        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.73            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.73          ( ( ![D:$i]:
% 0.52/0.73              ( ~( ( r2_hidden @ D @ B ) & 
% 0.52/0.73                   ( ![E:$i]:
% 0.52/0.73                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.52/0.73                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.52/0.73            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(dt_k2_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.52/0.73         ((m1_subset_1 @ (k2_relset_1 @ X25 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))
% 0.52/0.73          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 0.52/0.73        (k1_zfmisc_1 @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.52/0.73  thf('4', plain,
% 0.52/0.73      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.52/0.73         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.52/0.73          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.52/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['2', '5'])).
% 0.52/0.73  thf(t3_subset, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      (![X8 : $i, X9 : $i]:
% 0.52/0.73         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.73  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.52/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.73  thf(d10_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.73  thf('9', plain,
% 0.52/0.73      (![X4 : $i, X6 : $i]:
% 0.52/0.73         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.52/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.52/0.73        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.52/0.73  thf('11', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.52/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.73  thf('13', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('14', plain, (~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.52/0.73      inference('simplify_reflect-', [status(thm)], ['10', '13'])).
% 0.52/0.73  thf(d3_tarski, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X1 : $i, X3 : $i]:
% 0.52/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.73  thf('16', plain,
% 0.52/0.73      (![X42 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X42 @ sk_B)
% 0.52/0.73          | ((X42) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X42))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((r1_tarski @ sk_B @ X0)
% 0.52/0.73          | ((sk_C @ X0 @ sk_B)
% 0.52/0.73              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      (![X1 : $i, X3 : $i]:
% 0.52/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (![X42 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X42 @ sk_B) | (r2_hidden @ (sk_E @ X42) @ sk_A))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((r1_tarski @ sk_B @ X0)
% 0.52/0.73          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.73  thf('21', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(d1_funct_2, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.52/0.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.52/0.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.52/0.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_1, axiom,
% 0.52/0.73    (![C:$i,B:$i,A:$i]:
% 0.52/0.73     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.52/0.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.52/0.73         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.52/0.73          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.52/0.73          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.52/0.73        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.73  thf('24', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.52/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.73  thf(zf_stmt_2, axiom,
% 0.52/0.73    (![B:$i,A:$i]:
% 0.52/0.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.73       ( zip_tseitin_0 @ B @ A ) ))).
% 0.52/0.73  thf('25', plain,
% 0.52/0.73      (![X34 : $i, X35 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.73  thf(t4_subset_1, axiom,
% 0.52/0.73    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.73  thf('26', plain,
% 0.52/0.73      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.73  thf('27', plain,
% 0.52/0.73      (![X8 : $i, X9 : $i]:
% 0.52/0.73         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.73  thf('28', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.52/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.52/0.73  thf('29', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.52/0.73      inference('sup+', [status(thm)], ['25', '28'])).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.52/0.73  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.52/0.73  thf(zf_stmt_5, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.52/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.52/0.73  thf('31', plain,
% 0.52/0.73      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.52/0.73         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.52/0.73          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.52/0.73          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.73  thf('32', plain,
% 0.52/0.73      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.52/0.73        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['29', '32'])).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      (![X4 : $i, X6 : $i]:
% 0.52/0.73         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.52/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.73  thf('35', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.52/0.73          | ~ (r1_tarski @ X0 @ sk_B)
% 0.52/0.73          | ((X0) = (sk_B)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf('36', plain,
% 0.52/0.73      ((((k2_relat_1 @ sk_C_2) = (sk_B))
% 0.52/0.73        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['24', '35'])).
% 0.52/0.73  thf('37', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('38', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)),
% 0.52/0.73      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.52/0.73  thf('39', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.52/0.73         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.52/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.52/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.73  thf('42', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.52/0.73      inference('demod', [status(thm)], ['23', '38', '41'])).
% 0.52/0.73  thf(d5_funct_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.73       ( ![B:$i]:
% 0.52/0.73         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.52/0.73           ( ![C:$i]:
% 0.52/0.73             ( ( r2_hidden @ C @ B ) <=>
% 0.52/0.73               ( ?[D:$i]:
% 0.52/0.73                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.52/0.73                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.52/0.73  thf('43', plain,
% 0.52/0.73      (![X19 : $i, X21 : $i, X23 : $i, X24 : $i]:
% 0.52/0.73         (((X21) != (k2_relat_1 @ X19))
% 0.52/0.73          | (r2_hidden @ X23 @ X21)
% 0.52/0.73          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X19))
% 0.52/0.73          | ((X23) != (k1_funct_1 @ X19 @ X24))
% 0.52/0.73          | ~ (v1_funct_1 @ X19)
% 0.52/0.73          | ~ (v1_relat_1 @ X19))),
% 0.52/0.73      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.52/0.73  thf('44', plain,
% 0.52/0.73      (![X19 : $i, X24 : $i]:
% 0.52/0.73         (~ (v1_relat_1 @ X19)
% 0.52/0.73          | ~ (v1_funct_1 @ X19)
% 0.52/0.73          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X19))
% 0.52/0.73          | (r2_hidden @ (k1_funct_1 @ X19 @ X24) @ (k2_relat_1 @ X19)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['43'])).
% 0.52/0.73  thf('45', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X0 @ sk_A)
% 0.52/0.73          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.52/0.73          | ~ (v1_funct_1 @ sk_C_2)
% 0.52/0.73          | ~ (v1_relat_1 @ sk_C_2))),
% 0.52/0.73      inference('sup-', [status(thm)], ['42', '44'])).
% 0.52/0.73  thf('46', plain, ((v1_funct_1 @ sk_C_2)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('47', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(cc2_relat_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ A ) =>
% 0.52/0.73       ( ![B:$i]:
% 0.52/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.73  thf('48', plain,
% 0.52/0.73      (![X14 : $i, X15 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.52/0.73          | (v1_relat_1 @ X14)
% 0.52/0.73          | ~ (v1_relat_1 @ X15))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.73  thf('49', plain,
% 0.52/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.52/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.52/0.73  thf(fc6_relat_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.73  thf('50', plain,
% 0.52/0.73      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.73  thf('51', plain, ((v1_relat_1 @ sk_C_2)),
% 0.52/0.73      inference('demod', [status(thm)], ['49', '50'])).
% 0.52/0.73  thf('52', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X0 @ sk_A)
% 0.52/0.73          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.52/0.73      inference('demod', [status(thm)], ['45', '46', '51'])).
% 0.52/0.73  thf('53', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((r1_tarski @ sk_B @ X0)
% 0.52/0.73          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.52/0.73             (k2_relat_1 @ sk_C_2)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['20', '52'])).
% 0.52/0.73  thf('54', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 0.52/0.73          | (r1_tarski @ sk_B @ X0)
% 0.52/0.73          | (r1_tarski @ sk_B @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['17', '53'])).
% 0.52/0.73  thf('55', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((r1_tarski @ sk_B @ X0)
% 0.52/0.73          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['54'])).
% 0.52/0.73  thf('56', plain,
% 0.52/0.73      (![X1 : $i, X3 : $i]:
% 0.52/0.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.73  thf('57', plain,
% 0.52/0.73      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.52/0.73        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['55', '56'])).
% 0.52/0.73  thf('58', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.52/0.73      inference('simplify', [status(thm)], ['57'])).
% 0.52/0.73  thf('59', plain, ($false), inference('demod', [status(thm)], ['14', '58'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
