%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ml8HC3jU4B

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:08 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  232 (1410 expanded)
%              Number of leaves         :   47 ( 421 expanded)
%              Depth                    :   23
%              Number of atoms          : 1500 (16632 expanded)
%              Number of equality atoms :  120 (1168 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) @ X20 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) @ X20 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','17'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf(zf_stmt_0,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    ! [X35: $i] :
      ( zip_tseitin_0 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','36'])).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('43',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('44',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('45',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('61',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('65',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['38'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('87',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('95',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('97',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['38'])).

thf('98',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','99'])).

thf('101',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('102',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('103',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('104',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['38'])).

thf('109',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('110',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['85','100','107','108','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['82','110'])).

thf('112',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['73','111'])).

thf('113',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('117',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('119',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['112','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('122',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','17'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['120','125'])).

thf('127',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['40','126'])).

thf('128',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('129',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('130',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('131',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['128','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('134',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('135',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['133','134'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('136',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('139',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('141',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('142',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['137','142'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('144',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X33 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['140','141'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['132','147'])).

thf('149',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('150',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['38'])).

thf('152',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['85','150','151'])).

thf('153',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['127','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['132','147'])).

thf('155',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('156',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('158',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('160',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['132','147'])).

thf('161',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('162',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['132','147'])).

thf('164',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('165',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['112','119'])).

thf('167',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['38'])).

thf('172',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['85','150','151'])).

thf('173',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['170','173'])).

thf('175',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['162','174'])).

thf('176',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['159','175'])).

thf('177',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('178',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('179',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['159','175'])).

thf('180',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('181',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['158','176','177','178','179','180'])).

thf('182',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('183',plain,(
    $false ),
    inference(demod,[status(thm)],['153','181','182'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ml8HC3jU4B
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:51:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.86/1.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.86/1.05  % Solved by: fo/fo7.sh
% 0.86/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.05  % done 1147 iterations in 0.623s
% 0.86/1.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.86/1.05  % SZS output start Refutation
% 0.86/1.05  thf(sk_B_type, type, sk_B: $i > $i).
% 0.86/1.05  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.86/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.86/1.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.86/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.86/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.86/1.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.86/1.05  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.86/1.05  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.86/1.05  thf(sk_C_type, type, sk_C: $i).
% 0.86/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.86/1.05  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.86/1.05  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.86/1.05  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.86/1.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.86/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.86/1.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.86/1.05  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.86/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.86/1.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.86/1.05  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.86/1.05  thf(sk_D_type, type, sk_D: $i).
% 0.86/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.86/1.05  thf(t7_xboole_0, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.86/1.05          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.86/1.05  thf('0', plain,
% 0.86/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.86/1.05      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.86/1.05  thf(d10_xboole_0, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.86/1.05  thf('1', plain,
% 0.86/1.05      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.86/1.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.86/1.05  thf('2', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.86/1.05      inference('simplify', [status(thm)], ['1'])).
% 0.86/1.05  thf(t3_subset, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.86/1.05  thf('3', plain,
% 0.86/1.05      (![X8 : $i, X10 : $i]:
% 0.86/1.05         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.86/1.05      inference('cnf', [status(esa)], [t3_subset])).
% 0.86/1.05  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['2', '3'])).
% 0.86/1.05  thf(t5_subset, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.86/1.05          ( v1_xboole_0 @ C ) ) ))).
% 0.86/1.05  thf('5', plain,
% 0.86/1.05      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.86/1.05         (~ (r2_hidden @ X11 @ X12)
% 0.86/1.05          | ~ (v1_xboole_0 @ X13)
% 0.86/1.05          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t5_subset])).
% 0.86/1.05  thf('6', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['4', '5'])).
% 0.86/1.05  thf('7', plain,
% 0.86/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['0', '6'])).
% 0.86/1.05  thf('8', plain,
% 0.86/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['0', '6'])).
% 0.86/1.05  thf(t113_zfmisc_1, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.86/1.05       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.86/1.05  thf('9', plain,
% 0.86/1.05      (![X6 : $i, X7 : $i]:
% 0.86/1.05         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.86/1.05  thf('10', plain,
% 0.86/1.05      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['9'])).
% 0.86/1.05  thf(t193_relat_1, axiom,
% 0.86/1.05    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.86/1.05  thf('11', plain,
% 0.86/1.05      (![X20 : $i, X21 : $i]:
% 0.86/1.05         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21)) @ X20)),
% 0.86/1.05      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.86/1.05  thf('12', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.86/1.05      inference('sup+', [status(thm)], ['10', '11'])).
% 0.86/1.05  thf('13', plain,
% 0.86/1.05      (![X20 : $i, X21 : $i]:
% 0.86/1.05         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21)) @ X20)),
% 0.86/1.05      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.86/1.05  thf(t3_xboole_1, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.86/1.05  thf('14', plain,
% 0.86/1.05      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.86/1.05      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.86/1.05  thf('15', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((k1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['13', '14'])).
% 0.86/1.05  thf('16', plain,
% 0.86/1.05      (![X6 : $i, X7 : $i]:
% 0.86/1.05         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.86/1.05  thf('17', plain,
% 0.86/1.05      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['16'])).
% 0.86/1.05  thf('18', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.86/1.05      inference('demod', [status(thm)], ['15', '17'])).
% 0.86/1.05  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.86/1.05      inference('demod', [status(thm)], ['12', '18'])).
% 0.86/1.05  thf('20', plain,
% 0.86/1.05      (![X8 : $i, X10 : $i]:
% 0.86/1.05         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.86/1.05      inference('cnf', [status(esa)], [t3_subset])).
% 0.86/1.05  thf('21', plain,
% 0.86/1.05      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.86/1.05  thf(redefinition_k1_relset_1, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.86/1.05       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.86/1.05  thf('22', plain,
% 0.86/1.05      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.86/1.05         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.86/1.05          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.86/1.05      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.86/1.05  thf('23', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['21', '22'])).
% 0.86/1.05  thf('24', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.86/1.05      inference('demod', [status(thm)], ['15', '17'])).
% 0.86/1.05  thf('25', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.86/1.05      inference('demod', [status(thm)], ['23', '24'])).
% 0.86/1.05  thf(d1_funct_2, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.86/1.05       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.86/1.05           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.86/1.05             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.86/1.05         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.86/1.05           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.86/1.05             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.86/1.05  thf(zf_stmt_0, axiom,
% 0.86/1.05    (![C:$i,B:$i,A:$i]:
% 0.86/1.05     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.86/1.05       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.86/1.05  thf('26', plain,
% 0.86/1.05      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.86/1.05         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.86/1.05          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.86/1.05          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('27', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (((X1) != (k1_xboole_0))
% 0.86/1.05          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.86/1.05          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['25', '26'])).
% 0.86/1.05  thf('28', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.86/1.05          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['27'])).
% 0.86/1.05  thf(zf_stmt_1, axiom,
% 0.86/1.05    (![B:$i,A:$i]:
% 0.86/1.05     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.86/1.05       ( zip_tseitin_0 @ B @ A ) ))).
% 0.86/1.05  thf('29', plain,
% 0.86/1.05      (![X35 : $i, X36 : $i]:
% 0.86/1.05         ((zip_tseitin_0 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.86/1.05  thf('30', plain, (![X35 : $i]: (zip_tseitin_0 @ X35 @ k1_xboole_0)),
% 0.86/1.05      inference('simplify', [status(thm)], ['29'])).
% 0.86/1.05  thf('31', plain,
% 0.86/1.05      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['19', '20'])).
% 0.86/1.05  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.86/1.05  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.86/1.05  thf(zf_stmt_4, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.86/1.05       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.86/1.05         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.86/1.05           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.86/1.05             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.86/1.05  thf('32', plain,
% 0.86/1.05      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.86/1.05         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.86/1.05          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.86/1.05          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.86/1.05  thf('33', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.86/1.05      inference('sup-', [status(thm)], ['31', '32'])).
% 0.86/1.05  thf('34', plain,
% 0.86/1.05      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.86/1.05      inference('sup-', [status(thm)], ['30', '33'])).
% 0.86/1.05  thf('35', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.86/1.05      inference('demod', [status(thm)], ['28', '34'])).
% 0.86/1.05  thf('36', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.05      inference('sup+', [status(thm)], ['8', '35'])).
% 0.86/1.05  thf('37', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.05         ((v1_funct_2 @ X2 @ X0 @ X1)
% 0.86/1.05          | ~ (v1_xboole_0 @ X0)
% 0.86/1.05          | ~ (v1_xboole_0 @ X2))),
% 0.86/1.05      inference('sup+', [status(thm)], ['7', '36'])).
% 0.86/1.05  thf(t8_funct_2, conjecture,
% 0.86/1.05    (![A:$i,B:$i,C:$i,D:$i]:
% 0.86/1.05     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.86/1.05         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.86/1.05       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.86/1.05         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.86/1.05           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.86/1.05             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.86/1.05  thf(zf_stmt_5, negated_conjecture,
% 0.86/1.05    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.86/1.05        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.86/1.05            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.86/1.05          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.86/1.05            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.86/1.05              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.86/1.05                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.86/1.05    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.86/1.05  thf('38', plain,
% 0.86/1.05      ((~ (v1_funct_1 @ sk_D)
% 0.86/1.05        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.86/1.05        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf('39', plain,
% 0.86/1.05      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.86/1.05         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.86/1.05      inference('split', [status(esa)], ['38'])).
% 0.86/1.05  thf('40', plain,
% 0.86/1.05      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 0.86/1.05         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['37', '39'])).
% 0.86/1.05  thf('41', plain,
% 0.86/1.05      (![X35 : $i, X36 : $i]:
% 0.86/1.05         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.86/1.05  thf('42', plain,
% 0.86/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.86/1.05      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.86/1.05  thf('43', plain,
% 0.86/1.05      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['9'])).
% 0.86/1.05  thf(t29_relset_1, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( m1_subset_1 @
% 0.86/1.05       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.86/1.05  thf('44', plain,
% 0.86/1.05      (![X34 : $i]:
% 0.86/1.05         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 0.86/1.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.86/1.05  thf('45', plain,
% 0.86/1.05      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.86/1.05      inference('sup+', [status(thm)], ['43', '44'])).
% 0.86/1.05  thf('46', plain,
% 0.86/1.05      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.86/1.05         (~ (r2_hidden @ X11 @ X12)
% 0.86/1.05          | ~ (v1_xboole_0 @ X13)
% 0.86/1.05          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t5_subset])).
% 0.86/1.05  thf('47', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.86/1.05          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['45', '46'])).
% 0.86/1.05  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.86/1.05  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.86/1.05  thf('49', plain,
% 0.86/1.05      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 0.86/1.05      inference('demod', [status(thm)], ['47', '48'])).
% 0.86/1.05  thf('50', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['42', '49'])).
% 0.86/1.05  thf('51', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (((k6_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 0.86/1.05      inference('sup+', [status(thm)], ['41', '50'])).
% 0.86/1.05  thf('52', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf('53', plain,
% 0.86/1.05      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.86/1.05         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.86/1.05          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.86/1.05          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.86/1.05  thf('54', plain,
% 0.86/1.05      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.86/1.05        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['52', '53'])).
% 0.86/1.05  thf('55', plain,
% 0.86/1.05      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.86/1.05        | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['51', '54'])).
% 0.86/1.05  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf('57', plain,
% 0.86/1.05      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.86/1.05         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.86/1.05          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.86/1.05          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('58', plain,
% 0.86/1.05      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.86/1.05        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['56', '57'])).
% 0.86/1.05  thf('59', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf('60', plain,
% 0.86/1.05      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.86/1.05         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.86/1.05          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.86/1.05      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.86/1.05  thf('61', plain,
% 0.86/1.05      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.86/1.05      inference('sup-', [status(thm)], ['59', '60'])).
% 0.86/1.05  thf('62', plain,
% 0.86/1.05      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.86/1.05        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.86/1.05      inference('demod', [status(thm)], ['58', '61'])).
% 0.86/1.05  thf('63', plain,
% 0.86/1.05      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.86/1.05        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['55', '62'])).
% 0.86/1.05  thf('64', plain,
% 0.86/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['0', '6'])).
% 0.86/1.05  thf('65', plain,
% 0.86/1.05      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['16'])).
% 0.86/1.05  thf('66', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.05      inference('sup+', [status(thm)], ['64', '65'])).
% 0.86/1.05  thf('67', plain,
% 0.86/1.05      (![X34 : $i]:
% 0.86/1.05         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 0.86/1.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.86/1.05  thf('68', plain,
% 0.86/1.05      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.86/1.05         (~ (r2_hidden @ X11 @ X12)
% 0.86/1.05          | ~ (v1_xboole_0 @ X13)
% 0.86/1.05          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t5_subset])).
% 0.86/1.05  thf('69', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.86/1.05          | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['67', '68'])).
% 0.86/1.05  thf('70', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.86/1.05          | ~ (v1_xboole_0 @ X0)
% 0.86/1.05          | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['66', '69'])).
% 0.86/1.05  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.86/1.05  thf('72', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 0.86/1.05      inference('demod', [status(thm)], ['70', '71'])).
% 0.86/1.05  thf('73', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.86/1.05          | ((sk_A) = (k1_relat_1 @ sk_D))
% 0.86/1.05          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.86/1.05      inference('sup-', [status(thm)], ['63', '72'])).
% 0.86/1.05  thf('74', plain,
% 0.86/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['0', '6'])).
% 0.86/1.05  thf('75', plain,
% 0.86/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['0', '6'])).
% 0.86/1.05  thf('76', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.86/1.05      inference('sup+', [status(thm)], ['74', '75'])).
% 0.86/1.05  thf('77', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf('78', plain,
% 0.86/1.05      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.86/1.05      inference('split', [status(esa)], ['77'])).
% 0.86/1.05  thf('79', plain,
% 0.86/1.05      ((![X0 : $i]:
% 0.86/1.05          (((X0) != (k1_xboole_0))
% 0.86/1.05           | ~ (v1_xboole_0 @ X0)
% 0.86/1.05           | ~ (v1_xboole_0 @ sk_B_1)))
% 0.86/1.05         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['76', '78'])).
% 0.86/1.05  thf('80', plain,
% 0.86/1.05      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.86/1.05         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.86/1.05      inference('simplify', [status(thm)], ['79'])).
% 0.86/1.05  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.86/1.05  thf('82', plain,
% 0.86/1.05      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.86/1.05      inference('simplify_reflect+', [status(thm)], ['80', '81'])).
% 0.86/1.05  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf('84', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.86/1.05      inference('split', [status(esa)], ['38'])).
% 0.86/1.05  thf('85', plain, (((v1_funct_1 @ sk_D))),
% 0.86/1.05      inference('sup-', [status(thm)], ['83', '84'])).
% 0.86/1.05  thf('86', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.86/1.05      inference('demod', [status(thm)], ['28', '34'])).
% 0.86/1.05  thf('87', plain,
% 0.86/1.05      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['16'])).
% 0.86/1.05  thf('88', plain,
% 0.86/1.05      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('split', [status(esa)], ['77'])).
% 0.86/1.05  thf('89', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf('90', plain,
% 0.86/1.05      (((m1_subset_1 @ sk_D @ 
% 0.86/1.05         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.86/1.05         <= ((((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('sup+', [status(thm)], ['88', '89'])).
% 0.86/1.05  thf('91', plain,
% 0.86/1.05      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.86/1.05         <= ((((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('sup+', [status(thm)], ['87', '90'])).
% 0.86/1.05  thf('92', plain,
% 0.86/1.05      (![X8 : $i, X9 : $i]:
% 0.86/1.05         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t3_subset])).
% 0.86/1.05  thf('93', plain,
% 0.86/1.05      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['91', '92'])).
% 0.86/1.05  thf('94', plain,
% 0.86/1.05      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.86/1.05      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.86/1.05  thf('95', plain,
% 0.86/1.05      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['93', '94'])).
% 0.86/1.05  thf('96', plain,
% 0.86/1.05      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('split', [status(esa)], ['77'])).
% 0.86/1.05  thf('97', plain,
% 0.86/1.05      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.86/1.05         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.86/1.05      inference('split', [status(esa)], ['38'])).
% 0.86/1.05  thf('98', plain,
% 0.86/1.05      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.86/1.05         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['96', '97'])).
% 0.86/1.05  thf('99', plain,
% 0.86/1.05      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.86/1.05         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['95', '98'])).
% 0.86/1.05  thf('100', plain,
% 0.86/1.05      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['86', '99'])).
% 0.86/1.05  thf('101', plain,
% 0.86/1.05      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.86/1.05         <= ((((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('sup+', [status(thm)], ['87', '90'])).
% 0.86/1.05  thf('102', plain,
% 0.86/1.05      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['16'])).
% 0.86/1.05  thf('103', plain,
% 0.86/1.05      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('split', [status(esa)], ['77'])).
% 0.86/1.05  thf('104', plain,
% 0.86/1.05      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.86/1.05         <= (~
% 0.86/1.05             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.86/1.05      inference('split', [status(esa)], ['38'])).
% 0.86/1.05  thf('105', plain,
% 0.86/1.05      ((~ (m1_subset_1 @ sk_D @ 
% 0.86/1.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.86/1.05         <= (~
% 0.86/1.05             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.86/1.05             (((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['103', '104'])).
% 0.86/1.05  thf('106', plain,
% 0.86/1.05      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.86/1.05         <= (~
% 0.86/1.05             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.86/1.05             (((sk_A) = (k1_xboole_0))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['102', '105'])).
% 0.86/1.05  thf('107', plain,
% 0.86/1.05      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.86/1.05       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['101', '106'])).
% 0.86/1.05  thf('108', plain,
% 0.86/1.05      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.86/1.05       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.86/1.05      inference('split', [status(esa)], ['38'])).
% 0.86/1.05  thf('109', plain,
% 0.86/1.05      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.86/1.05      inference('split', [status(esa)], ['77'])).
% 0.86/1.05  thf('110', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.86/1.05      inference('sat_resolution*', [status(thm)],
% 0.86/1.05                ['85', '100', '107', '108', '109'])).
% 0.86/1.05  thf('111', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.86/1.05      inference('simpl_trail', [status(thm)], ['82', '110'])).
% 0.86/1.05  thf('112', plain,
% 0.86/1.05      ((~ (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.86/1.05      inference('clc', [status(thm)], ['73', '111'])).
% 0.86/1.05  thf('113', plain,
% 0.86/1.05      (![X35 : $i, X36 : $i]:
% 0.86/1.05         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.86/1.05  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.86/1.05  thf('115', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.86/1.05      inference('sup+', [status(thm)], ['113', '114'])).
% 0.86/1.05  thf('116', plain,
% 0.86/1.05      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.86/1.05        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['52', '53'])).
% 0.86/1.05  thf('117', plain,
% 0.86/1.05      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['115', '116'])).
% 0.86/1.05  thf('118', plain,
% 0.86/1.05      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.86/1.05        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.86/1.05      inference('demod', [status(thm)], ['58', '61'])).
% 0.86/1.05  thf('119', plain,
% 0.86/1.05      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['117', '118'])).
% 0.86/1.05  thf('120', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.86/1.05      inference('clc', [status(thm)], ['112', '119'])).
% 0.86/1.05  thf('121', plain,
% 0.86/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['0', '6'])).
% 0.86/1.05  thf('122', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.86/1.05      inference('demod', [status(thm)], ['15', '17'])).
% 0.86/1.05  thf('123', plain,
% 0.86/1.05      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.05      inference('sup+', [status(thm)], ['121', '122'])).
% 0.86/1.05  thf('124', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.86/1.05  thf('125', plain,
% 0.86/1.05      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.05      inference('sup+', [status(thm)], ['123', '124'])).
% 0.86/1.05  thf('126', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 0.86/1.05      inference('sup+', [status(thm)], ['120', '125'])).
% 0.86/1.05  thf('127', plain,
% 0.86/1.05      ((~ (v1_xboole_0 @ sk_D)) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.86/1.05      inference('clc', [status(thm)], ['40', '126'])).
% 0.86/1.05  thf('128', plain,
% 0.86/1.05      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf('129', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf(redefinition_k2_relset_1, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.86/1.05       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.86/1.05  thf('130', plain,
% 0.86/1.05      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.86/1.05         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.86/1.05          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.86/1.05      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.86/1.05  thf('131', plain,
% 0.86/1.05      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.86/1.05      inference('sup-', [status(thm)], ['129', '130'])).
% 0.86/1.05  thf('132', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.86/1.05      inference('demod', [status(thm)], ['128', '131'])).
% 0.86/1.05  thf('133', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf(cc2_relset_1, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.86/1.05       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.86/1.05  thf('134', plain,
% 0.86/1.05      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.86/1.05         ((v4_relat_1 @ X22 @ X23)
% 0.86/1.05          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.86/1.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.86/1.05  thf('135', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.86/1.05      inference('sup-', [status(thm)], ['133', '134'])).
% 0.86/1.05  thf(d18_relat_1, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( v1_relat_1 @ B ) =>
% 0.86/1.05       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.86/1.05  thf('136', plain,
% 0.86/1.05      (![X16 : $i, X17 : $i]:
% 0.86/1.05         (~ (v4_relat_1 @ X16 @ X17)
% 0.86/1.05          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.86/1.05          | ~ (v1_relat_1 @ X16))),
% 0.86/1.05      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.86/1.05  thf('137', plain,
% 0.86/1.05      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['135', '136'])).
% 0.86/1.05  thf('138', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.86/1.05  thf(cc2_relat_1, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( v1_relat_1 @ A ) =>
% 0.86/1.05       ( ![B:$i]:
% 0.86/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.86/1.05  thf('139', plain,
% 0.86/1.05      (![X14 : $i, X15 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.86/1.05          | (v1_relat_1 @ X14)
% 0.86/1.05          | ~ (v1_relat_1 @ X15))),
% 0.86/1.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.86/1.05  thf('140', plain,
% 0.86/1.05      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.86/1.05      inference('sup-', [status(thm)], ['138', '139'])).
% 0.86/1.05  thf(fc6_relat_1, axiom,
% 0.86/1.05    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.86/1.05  thf('141', plain,
% 0.86/1.05      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.86/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.86/1.05  thf('142', plain, ((v1_relat_1 @ sk_D)),
% 0.86/1.05      inference('demod', [status(thm)], ['140', '141'])).
% 0.86/1.05  thf('143', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.86/1.05      inference('demod', [status(thm)], ['137', '142'])).
% 0.86/1.05  thf(t11_relset_1, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ( v1_relat_1 @ C ) =>
% 0.86/1.05       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.86/1.05           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.86/1.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.86/1.05  thf('144', plain,
% 0.86/1.05      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.86/1.05         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 0.86/1.05          | ~ (r1_tarski @ (k2_relat_1 @ X31) @ X33)
% 0.86/1.05          | (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.86/1.05          | ~ (v1_relat_1 @ X31))),
% 0.86/1.05      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.86/1.05  thf('145', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         (~ (v1_relat_1 @ sk_D)
% 0.86/1.05          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.86/1.05          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['143', '144'])).
% 0.86/1.05  thf('146', plain, ((v1_relat_1 @ sk_D)),
% 0.86/1.05      inference('demod', [status(thm)], ['140', '141'])).
% 0.86/1.05  thf('147', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.86/1.05          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.86/1.05      inference('demod', [status(thm)], ['145', '146'])).
% 0.86/1.05  thf('148', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['132', '147'])).
% 0.86/1.05  thf('149', plain,
% 0.86/1.05      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.86/1.05         <= (~
% 0.86/1.05             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.86/1.05      inference('split', [status(esa)], ['38'])).
% 0.86/1.05  thf('150', plain,
% 0.86/1.05      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['148', '149'])).
% 0.86/1.05  thf('151', plain,
% 0.86/1.05      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.86/1.05       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.86/1.05       ~ ((v1_funct_1 @ sk_D))),
% 0.86/1.05      inference('split', [status(esa)], ['38'])).
% 0.86/1.05  thf('152', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.86/1.05      inference('sat_resolution*', [status(thm)], ['85', '150', '151'])).
% 0.86/1.05  thf('153', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.86/1.05      inference('simpl_trail', [status(thm)], ['127', '152'])).
% 0.86/1.05  thf('154', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['132', '147'])).
% 0.86/1.05  thf('155', plain,
% 0.86/1.05      (![X8 : $i, X9 : $i]:
% 0.86/1.05         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t3_subset])).
% 0.86/1.05  thf('156', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.86/1.05      inference('sup-', [status(thm)], ['154', '155'])).
% 0.86/1.05  thf('157', plain,
% 0.86/1.05      (![X1 : $i, X3 : $i]:
% 0.86/1.05         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.86/1.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.86/1.05  thf('158', plain,
% 0.86/1.05      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 0.86/1.05        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['156', '157'])).
% 0.86/1.05  thf('159', plain,
% 0.86/1.05      (![X35 : $i, X36 : $i]:
% 0.86/1.05         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.86/1.05  thf('160', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['132', '147'])).
% 0.86/1.05  thf('161', plain,
% 0.86/1.05      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.86/1.05         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.86/1.05          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.86/1.05          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.86/1.05  thf('162', plain,
% 0.86/1.05      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['160', '161'])).
% 0.86/1.05  thf('163', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['132', '147'])).
% 0.86/1.05  thf('164', plain,
% 0.86/1.05      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.86/1.05         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.86/1.05          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.86/1.05      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.86/1.05  thf('165', plain,
% 0.86/1.05      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.86/1.05      inference('sup-', [status(thm)], ['163', '164'])).
% 0.86/1.05  thf('166', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.86/1.05      inference('clc', [status(thm)], ['112', '119'])).
% 0.86/1.05  thf('167', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.86/1.05      inference('demod', [status(thm)], ['165', '166'])).
% 0.86/1.05  thf('168', plain,
% 0.86/1.05      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.86/1.05         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.86/1.05          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.86/1.05          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('169', plain,
% 0.86/1.05      ((((sk_A) != (sk_A))
% 0.86/1.05        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.86/1.05        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.86/1.05      inference('sup-', [status(thm)], ['167', '168'])).
% 0.86/1.05  thf('170', plain,
% 0.86/1.05      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.86/1.05        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.86/1.05      inference('simplify', [status(thm)], ['169'])).
% 0.86/1.05  thf('171', plain,
% 0.86/1.05      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.86/1.05         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.86/1.05      inference('split', [status(esa)], ['38'])).
% 0.86/1.05  thf('172', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.86/1.05      inference('sat_resolution*', [status(thm)], ['85', '150', '151'])).
% 0.86/1.05  thf('173', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.86/1.05      inference('simpl_trail', [status(thm)], ['171', '172'])).
% 0.86/1.05  thf('174', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.86/1.05      inference('clc', [status(thm)], ['170', '173'])).
% 0.86/1.05  thf('175', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 0.86/1.05      inference('clc', [status(thm)], ['162', '174'])).
% 0.86/1.05  thf('176', plain, (((sk_C) = (k1_xboole_0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['159', '175'])).
% 0.86/1.05  thf('177', plain,
% 0.86/1.05      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['9'])).
% 0.86/1.05  thf('178', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.86/1.05      inference('demod', [status(thm)], ['12', '18'])).
% 0.86/1.05  thf('179', plain, (((sk_C) = (k1_xboole_0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['159', '175'])).
% 0.86/1.05  thf('180', plain,
% 0.86/1.05      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.86/1.05      inference('simplify', [status(thm)], ['9'])).
% 0.86/1.05  thf('181', plain, (((k1_xboole_0) = (sk_D))),
% 0.86/1.05      inference('demod', [status(thm)],
% 0.86/1.05                ['158', '176', '177', '178', '179', '180'])).
% 0.86/1.05  thf('182', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.86/1.05  thf('183', plain, ($false),
% 0.86/1.05      inference('demod', [status(thm)], ['153', '181', '182'])).
% 0.86/1.05  
% 0.86/1.05  % SZS output end Refutation
% 0.86/1.05  
% 0.86/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
