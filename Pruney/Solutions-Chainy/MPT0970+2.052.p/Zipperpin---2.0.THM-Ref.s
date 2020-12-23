%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kvE10oxMq0

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:24 EST 2020

% Result     : Theorem 6.64s
% Output     : Refutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :  130 (1479 expanded)
%              Number of leaves         :   41 ( 441 expanded)
%              Depth                    :   25
%              Number of atoms          : 1042 (20749 expanded)
%              Number of equality atoms :   70 (1283 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( ( sk_C_1 @ X11 @ X12 )
        = ( k1_funct_1 @ X12 @ ( sk_D @ X11 @ X12 ) ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( r2_hidden @ ( sk_D @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X12: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X17 ) @ ( k2_relat_1 @ X12 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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

thf('32',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','30'])).

thf('46',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( X37
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_C_1 @ sk_B @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','30'])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( ( sk_C_1 @ X11 @ X12 )
       != ( k1_funct_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['26','29'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_C_2 )
     != ( sk_C_1 @ sk_B @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','57'])).

thf('59',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','30'])).

thf('60',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X37 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','61'])).

thf('64',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['31','62','63'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('65',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('70',plain,(
    ! [X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X12 ) @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('73',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( X15
        = ( k1_funct_1 @ X12 @ ( sk_D_1 @ X15 @ X12 ) ) )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('74',plain,(
    ! [X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X12 ) )
      | ( X15
        = ( k1_funct_1 @ X12 @ ( sk_D_1 @ X15 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ k1_xboole_0 @ sk_C_2 )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('77',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','61'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ k1_xboole_0 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_C_2 )
     != ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('81',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_C_2 )
     != ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_C_2 ) @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['71','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('86',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['84','85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kvE10oxMq0
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 6.64/6.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.64/6.84  % Solved by: fo/fo7.sh
% 6.64/6.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.64/6.84  % done 1855 iterations in 6.381s
% 6.64/6.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.64/6.84  % SZS output start Refutation
% 6.64/6.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.64/6.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.64/6.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.64/6.84  thf(sk_A_type, type, sk_A: $i).
% 6.64/6.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.64/6.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.64/6.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.64/6.84  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 6.64/6.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.64/6.84  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.64/6.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.64/6.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.64/6.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.64/6.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.64/6.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.64/6.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.64/6.84  thf(sk_E_type, type, sk_E: $i > $i).
% 6.64/6.84  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 6.64/6.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.64/6.84  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.64/6.84  thf(sk_B_type, type, sk_B: $i).
% 6.64/6.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.64/6.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.64/6.84  thf(sk_C_2_type, type, sk_C_2: $i).
% 6.64/6.84  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.64/6.84  thf(d5_funct_1, axiom,
% 6.64/6.84    (![A:$i]:
% 6.64/6.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.64/6.84       ( ![B:$i]:
% 6.64/6.84         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 6.64/6.84           ( ![C:$i]:
% 6.64/6.84             ( ( r2_hidden @ C @ B ) <=>
% 6.64/6.84               ( ?[D:$i]:
% 6.64/6.84                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 6.64/6.84                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 6.64/6.84  thf('0', plain,
% 6.64/6.84      (![X11 : $i, X12 : $i]:
% 6.64/6.84         ((r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 6.64/6.84          | ((sk_C_1 @ X11 @ X12) = (k1_funct_1 @ X12 @ (sk_D @ X11 @ X12)))
% 6.64/6.84          | ((X11) = (k2_relat_1 @ X12))
% 6.64/6.84          | ~ (v1_funct_1 @ X12)
% 6.64/6.84          | ~ (v1_relat_1 @ X12))),
% 6.64/6.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 6.64/6.84  thf('1', plain,
% 6.64/6.84      (![X11 : $i, X12 : $i]:
% 6.64/6.84         ((r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 6.64/6.84          | (r2_hidden @ (sk_D @ X11 @ X12) @ (k1_relat_1 @ X12))
% 6.64/6.84          | ((X11) = (k2_relat_1 @ X12))
% 6.64/6.84          | ~ (v1_funct_1 @ X12)
% 6.64/6.84          | ~ (v1_relat_1 @ X12))),
% 6.64/6.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 6.64/6.84  thf('2', plain,
% 6.64/6.84      (![X12 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 6.64/6.84         (((X14) != (k2_relat_1 @ X12))
% 6.64/6.84          | (r2_hidden @ X16 @ X14)
% 6.64/6.84          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 6.64/6.84          | ((X16) != (k1_funct_1 @ X12 @ X17))
% 6.64/6.84          | ~ (v1_funct_1 @ X12)
% 6.64/6.84          | ~ (v1_relat_1 @ X12))),
% 6.64/6.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 6.64/6.84  thf('3', plain,
% 6.64/6.84      (![X12 : $i, X17 : $i]:
% 6.64/6.84         (~ (v1_relat_1 @ X12)
% 6.64/6.84          | ~ (v1_funct_1 @ X12)
% 6.64/6.84          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 6.64/6.84          | (r2_hidden @ (k1_funct_1 @ X12 @ X17) @ (k2_relat_1 @ X12)))),
% 6.64/6.84      inference('simplify', [status(thm)], ['2'])).
% 6.64/6.84  thf('4', plain,
% 6.64/6.84      (![X0 : $i, X1 : $i]:
% 6.64/6.84         (~ (v1_relat_1 @ X0)
% 6.64/6.84          | ~ (v1_funct_1 @ X0)
% 6.64/6.84          | ((X1) = (k2_relat_1 @ X0))
% 6.64/6.84          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 6.64/6.84          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 6.64/6.84             (k2_relat_1 @ X0))
% 6.64/6.84          | ~ (v1_funct_1 @ X0)
% 6.64/6.84          | ~ (v1_relat_1 @ X0))),
% 6.64/6.84      inference('sup-', [status(thm)], ['1', '3'])).
% 6.64/6.84  thf('5', plain,
% 6.64/6.84      (![X0 : $i, X1 : $i]:
% 6.64/6.84         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 6.64/6.84          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 6.64/6.84          | ((X1) = (k2_relat_1 @ X0))
% 6.64/6.84          | ~ (v1_funct_1 @ X0)
% 6.64/6.84          | ~ (v1_relat_1 @ X0))),
% 6.64/6.84      inference('simplify', [status(thm)], ['4'])).
% 6.64/6.84  thf('6', plain,
% 6.64/6.84      (![X0 : $i, X1 : $i]:
% 6.64/6.84         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 6.64/6.84          | ~ (v1_relat_1 @ X0)
% 6.64/6.84          | ~ (v1_funct_1 @ X0)
% 6.64/6.84          | ((X1) = (k2_relat_1 @ X0))
% 6.64/6.84          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 6.64/6.84          | ~ (v1_relat_1 @ X0)
% 6.64/6.84          | ~ (v1_funct_1 @ X0)
% 6.64/6.84          | ((X1) = (k2_relat_1 @ X0))
% 6.64/6.84          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 6.64/6.84      inference('sup+', [status(thm)], ['0', '5'])).
% 6.64/6.84  thf('7', plain,
% 6.64/6.84      (![X0 : $i, X1 : $i]:
% 6.64/6.84         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 6.64/6.84          | ((X1) = (k2_relat_1 @ X0))
% 6.64/6.84          | ~ (v1_funct_1 @ X0)
% 6.64/6.84          | ~ (v1_relat_1 @ X0)
% 6.64/6.84          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 6.64/6.84      inference('simplify', [status(thm)], ['6'])).
% 6.64/6.84  thf(t16_funct_2, conjecture,
% 6.64/6.84    (![A:$i,B:$i,C:$i]:
% 6.64/6.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.64/6.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.64/6.84       ( ( ![D:$i]:
% 6.64/6.84           ( ~( ( r2_hidden @ D @ B ) & 
% 6.64/6.84                ( ![E:$i]:
% 6.64/6.84                  ( ~( ( r2_hidden @ E @ A ) & 
% 6.64/6.84                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 6.64/6.84         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 6.64/6.84  thf(zf_stmt_0, negated_conjecture,
% 6.64/6.84    (~( ![A:$i,B:$i,C:$i]:
% 6.64/6.84        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.64/6.84            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.64/6.84          ( ( ![D:$i]:
% 6.64/6.84              ( ~( ( r2_hidden @ D @ B ) & 
% 6.64/6.84                   ( ![E:$i]:
% 6.64/6.84                     ( ~( ( r2_hidden @ E @ A ) & 
% 6.64/6.84                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 6.64/6.84            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 6.64/6.84    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 6.64/6.84  thf('8', plain,
% 6.64/6.84      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.84  thf(cc2_relset_1, axiom,
% 6.64/6.84    (![A:$i,B:$i,C:$i]:
% 6.64/6.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.84       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.64/6.84  thf('9', plain,
% 6.64/6.84      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.64/6.84         ((v5_relat_1 @ X20 @ X22)
% 6.64/6.84          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.64/6.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.64/6.84  thf('10', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 6.64/6.84      inference('sup-', [status(thm)], ['8', '9'])).
% 6.64/6.84  thf(d19_relat_1, axiom,
% 6.64/6.84    (![A:$i,B:$i]:
% 6.64/6.84     ( ( v1_relat_1 @ B ) =>
% 6.64/6.84       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 6.64/6.84  thf('11', plain,
% 6.64/6.84      (![X7 : $i, X8 : $i]:
% 6.64/6.84         (~ (v5_relat_1 @ X7 @ X8)
% 6.64/6.84          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 6.64/6.84          | ~ (v1_relat_1 @ X7))),
% 6.64/6.84      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.64/6.84  thf('12', plain,
% 6.64/6.84      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 6.64/6.84      inference('sup-', [status(thm)], ['10', '11'])).
% 6.64/6.84  thf('13', plain,
% 6.64/6.84      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.84  thf(cc2_relat_1, axiom,
% 6.64/6.84    (![A:$i]:
% 6.64/6.84     ( ( v1_relat_1 @ A ) =>
% 6.64/6.84       ( ![B:$i]:
% 6.64/6.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.64/6.84  thf('14', plain,
% 6.64/6.84      (![X5 : $i, X6 : $i]:
% 6.64/6.84         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 6.64/6.84          | (v1_relat_1 @ X5)
% 6.64/6.84          | ~ (v1_relat_1 @ X6))),
% 6.64/6.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.64/6.84  thf('15', plain,
% 6.64/6.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 6.64/6.84      inference('sup-', [status(thm)], ['13', '14'])).
% 6.64/6.84  thf(fc6_relat_1, axiom,
% 6.64/6.84    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.64/6.84  thf('16', plain,
% 6.64/6.84      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 6.64/6.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.64/6.84  thf('17', plain, ((v1_relat_1 @ sk_C_2)),
% 6.64/6.84      inference('demod', [status(thm)], ['15', '16'])).
% 6.64/6.84  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 6.64/6.84      inference('demod', [status(thm)], ['12', '17'])).
% 6.64/6.84  thf(d3_tarski, axiom,
% 6.64/6.84    (![A:$i,B:$i]:
% 6.64/6.84     ( ( r1_tarski @ A @ B ) <=>
% 6.64/6.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.64/6.84  thf('19', plain,
% 6.64/6.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.64/6.84         (~ (r2_hidden @ X0 @ X1)
% 6.64/6.84          | (r2_hidden @ X0 @ X2)
% 6.64/6.84          | ~ (r1_tarski @ X1 @ X2))),
% 6.64/6.84      inference('cnf', [status(esa)], [d3_tarski])).
% 6.64/6.84  thf('20', plain,
% 6.64/6.84      (![X0 : $i]:
% 6.64/6.84         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 6.64/6.84      inference('sup-', [status(thm)], ['18', '19'])).
% 6.64/6.84  thf('21', plain,
% 6.64/6.84      (![X0 : $i]:
% 6.64/6.84         (~ (v1_relat_1 @ sk_C_2)
% 6.64/6.84          | ~ (v1_funct_1 @ sk_C_2)
% 6.64/6.84          | ((X0) = (k2_relat_1 @ sk_C_2))
% 6.64/6.84          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 6.64/6.84          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 6.64/6.84      inference('sup-', [status(thm)], ['7', '20'])).
% 6.64/6.84  thf('22', plain, ((v1_relat_1 @ sk_C_2)),
% 6.64/6.84      inference('demod', [status(thm)], ['15', '16'])).
% 6.64/6.84  thf('23', plain, ((v1_funct_1 @ sk_C_2)),
% 6.64/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.84  thf('24', plain,
% 6.64/6.84      (![X0 : $i]:
% 6.64/6.84         (((X0) = (k2_relat_1 @ sk_C_2))
% 6.64/6.84          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 6.64/6.84          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 6.64/6.84      inference('demod', [status(thm)], ['21', '22', '23'])).
% 6.64/6.84  thf('25', plain,
% 6.64/6.84      (((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 6.64/6.84        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 6.64/6.84      inference('eq_fact', [status(thm)], ['24'])).
% 6.64/6.84  thf('26', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 6.64/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.84  thf('27', plain,
% 6.64/6.84      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.84  thf(redefinition_k2_relset_1, axiom,
% 6.64/6.84    (![A:$i,B:$i,C:$i]:
% 6.64/6.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.64/6.84  thf('28', plain,
% 6.64/6.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.64/6.84         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 6.64/6.84          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 6.64/6.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.64/6.84  thf('29', plain,
% 6.64/6.84      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 6.64/6.84      inference('sup-', [status(thm)], ['27', '28'])).
% 6.64/6.84  thf('30', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 6.64/6.84      inference('demod', [status(thm)], ['26', '29'])).
% 6.64/6.84  thf('31', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 6.64/6.85      inference('simplify_reflect-', [status(thm)], ['25', '30'])).
% 6.64/6.85  thf(d1_funct_2, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.85       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.64/6.85           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.64/6.85             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.64/6.85         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.64/6.85           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.64/6.85             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.64/6.85  thf(zf_stmt_1, axiom,
% 6.64/6.85    (![B:$i,A:$i]:
% 6.64/6.85     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.64/6.85       ( zip_tseitin_0 @ B @ A ) ))).
% 6.64/6.85  thf('32', plain,
% 6.64/6.85      (![X29 : $i, X30 : $i]:
% 6.64/6.85         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.64/6.85  thf('33', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.64/6.85  thf(zf_stmt_3, axiom,
% 6.64/6.85    (![C:$i,B:$i,A:$i]:
% 6.64/6.85     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.64/6.85       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.64/6.85  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.64/6.85  thf(zf_stmt_5, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.85       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.64/6.85         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.64/6.85           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.64/6.85             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.64/6.85  thf('34', plain,
% 6.64/6.85      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.64/6.85         (~ (zip_tseitin_0 @ X34 @ X35)
% 6.64/6.85          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 6.64/6.85          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.64/6.85  thf('35', plain,
% 6.64/6.85      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 6.64/6.85        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.64/6.85      inference('sup-', [status(thm)], ['33', '34'])).
% 6.64/6.85  thf('36', plain,
% 6.64/6.85      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 6.64/6.85      inference('sup-', [status(thm)], ['32', '35'])).
% 6.64/6.85  thf('37', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('38', plain,
% 6.64/6.85      (![X31 : $i, X32 : $i, X33 : $i]:
% 6.64/6.85         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 6.64/6.85          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 6.64/6.85          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.64/6.85  thf('39', plain,
% 6.64/6.85      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 6.64/6.85        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['37', '38'])).
% 6.64/6.85  thf('40', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(redefinition_k1_relset_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.64/6.85       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.64/6.85  thf('41', plain,
% 6.64/6.85      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.64/6.85         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 6.64/6.85          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 6.64/6.85      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.64/6.85  thf('42', plain,
% 6.64/6.85      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 6.64/6.85      inference('sup-', [status(thm)], ['40', '41'])).
% 6.64/6.85  thf('43', plain,
% 6.64/6.85      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 6.64/6.85        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.64/6.85      inference('demod', [status(thm)], ['39', '42'])).
% 6.64/6.85  thf('44', plain,
% 6.64/6.85      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['36', '43'])).
% 6.64/6.85  thf('45', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 6.64/6.85      inference('simplify_reflect-', [status(thm)], ['25', '30'])).
% 6.64/6.85  thf('46', plain,
% 6.64/6.85      (![X37 : $i]:
% 6.64/6.85         (~ (r2_hidden @ X37 @ sk_B)
% 6.64/6.85          | ((X37) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X37))))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('47', plain,
% 6.64/6.85      (((sk_C_1 @ sk_B @ sk_C_2)
% 6.64/6.85         = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2))))),
% 6.64/6.85      inference('sup-', [status(thm)], ['45', '46'])).
% 6.64/6.85  thf('48', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 6.64/6.85      inference('simplify_reflect-', [status(thm)], ['25', '30'])).
% 6.64/6.85  thf('49', plain,
% 6.64/6.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.64/6.85         (~ (r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 6.64/6.85          | ((sk_C_1 @ X11 @ X12) != (k1_funct_1 @ X12 @ X13))
% 6.64/6.85          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 6.64/6.85          | ((X11) = (k2_relat_1 @ X12))
% 6.64/6.85          | ~ (v1_funct_1 @ X12)
% 6.64/6.85          | ~ (v1_relat_1 @ X12))),
% 6.64/6.85      inference('cnf', [status(esa)], [d5_funct_1])).
% 6.64/6.85  thf('50', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (~ (v1_relat_1 @ sk_C_2)
% 6.64/6.85          | ~ (v1_funct_1 @ sk_C_2)
% 6.64/6.85          | ((sk_B) = (k2_relat_1 @ sk_C_2))
% 6.64/6.85          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 6.64/6.85          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['48', '49'])).
% 6.64/6.85  thf('51', plain, ((v1_relat_1 @ sk_C_2)),
% 6.64/6.85      inference('demod', [status(thm)], ['15', '16'])).
% 6.64/6.85  thf('52', plain, ((v1_funct_1 @ sk_C_2)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('53', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (((sk_B) = (k2_relat_1 @ sk_C_2))
% 6.64/6.85          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 6.64/6.85          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 6.64/6.85      inference('demod', [status(thm)], ['50', '51', '52'])).
% 6.64/6.85  thf('54', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 6.64/6.85      inference('demod', [status(thm)], ['26', '29'])).
% 6.64/6.85  thf('55', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 6.64/6.85          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 6.64/6.85      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 6.64/6.85  thf('56', plain,
% 6.64/6.85      ((((sk_C_1 @ sk_B @ sk_C_2) != (sk_C_1 @ sk_B @ sk_C_2))
% 6.64/6.85        | ~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ 
% 6.64/6.85             (k1_relat_1 @ sk_C_2)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['47', '55'])).
% 6.64/6.85  thf('57', plain,
% 6.64/6.85      (~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ (k1_relat_1 @ sk_C_2))),
% 6.64/6.85      inference('simplify', [status(thm)], ['56'])).
% 6.64/6.85  thf('58', plain,
% 6.64/6.85      ((~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A)
% 6.64/6.85        | ((sk_B) = (k1_xboole_0)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['44', '57'])).
% 6.64/6.85  thf('59', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 6.64/6.85      inference('simplify_reflect-', [status(thm)], ['25', '30'])).
% 6.64/6.85  thf('60', plain,
% 6.64/6.85      (![X37 : $i]:
% 6.64/6.85         (~ (r2_hidden @ X37 @ sk_B) | (r2_hidden @ (sk_E @ X37) @ sk_A))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('61', plain, ((r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A)),
% 6.64/6.85      inference('sup-', [status(thm)], ['59', '60'])).
% 6.64/6.85  thf('62', plain, (((sk_B) = (k1_xboole_0))),
% 6.64/6.85      inference('demod', [status(thm)], ['58', '61'])).
% 6.64/6.85  thf('63', plain, (((sk_B) = (k1_xboole_0))),
% 6.64/6.85      inference('demod', [status(thm)], ['58', '61'])).
% 6.64/6.85  thf('64', plain,
% 6.64/6.85      ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ k1_xboole_0)),
% 6.64/6.85      inference('demod', [status(thm)], ['31', '62', '63'])).
% 6.64/6.85  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.64/6.85  thf('65', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 6.64/6.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.64/6.85  thf('66', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.64/6.85         (~ (r2_hidden @ X0 @ X1)
% 6.64/6.85          | (r2_hidden @ X0 @ X2)
% 6.64/6.85          | ~ (r1_tarski @ X1 @ X2))),
% 6.64/6.85      inference('cnf', [status(esa)], [d3_tarski])).
% 6.64/6.85  thf('67', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i]:
% 6.64/6.85         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 6.64/6.85      inference('sup-', [status(thm)], ['65', '66'])).
% 6.64/6.85  thf('68', plain,
% 6.64/6.85      (![X0 : $i]: (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ X0)),
% 6.64/6.85      inference('sup-', [status(thm)], ['64', '67'])).
% 6.64/6.85  thf('69', plain,
% 6.64/6.85      (![X12 : $i, X14 : $i, X15 : $i]:
% 6.64/6.85         (((X14) != (k2_relat_1 @ X12))
% 6.64/6.85          | (r2_hidden @ (sk_D_1 @ X15 @ X12) @ (k1_relat_1 @ X12))
% 6.64/6.85          | ~ (r2_hidden @ X15 @ X14)
% 6.64/6.85          | ~ (v1_funct_1 @ X12)
% 6.64/6.85          | ~ (v1_relat_1 @ X12))),
% 6.64/6.85      inference('cnf', [status(esa)], [d5_funct_1])).
% 6.64/6.85  thf('70', plain,
% 6.64/6.85      (![X12 : $i, X15 : $i]:
% 6.64/6.85         (~ (v1_relat_1 @ X12)
% 6.64/6.85          | ~ (v1_funct_1 @ X12)
% 6.64/6.85          | ~ (r2_hidden @ X15 @ (k2_relat_1 @ X12))
% 6.64/6.85          | (r2_hidden @ (sk_D_1 @ X15 @ X12) @ (k1_relat_1 @ X12)))),
% 6.64/6.85      inference('simplify', [status(thm)], ['69'])).
% 6.64/6.85  thf('71', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ X0) @ 
% 6.64/6.85           (k1_relat_1 @ X0))
% 6.64/6.85          | ~ (v1_funct_1 @ X0)
% 6.64/6.85          | ~ (v1_relat_1 @ X0))),
% 6.64/6.85      inference('sup-', [status(thm)], ['68', '70'])).
% 6.64/6.85  thf('72', plain,
% 6.64/6.85      (![X0 : $i]: (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ X0)),
% 6.64/6.85      inference('sup-', [status(thm)], ['64', '67'])).
% 6.64/6.85  thf('73', plain,
% 6.64/6.85      (![X12 : $i, X14 : $i, X15 : $i]:
% 6.64/6.85         (((X14) != (k2_relat_1 @ X12))
% 6.64/6.85          | ((X15) = (k1_funct_1 @ X12 @ (sk_D_1 @ X15 @ X12)))
% 6.64/6.85          | ~ (r2_hidden @ X15 @ X14)
% 6.64/6.85          | ~ (v1_funct_1 @ X12)
% 6.64/6.85          | ~ (v1_relat_1 @ X12))),
% 6.64/6.85      inference('cnf', [status(esa)], [d5_funct_1])).
% 6.64/6.85  thf('74', plain,
% 6.64/6.85      (![X12 : $i, X15 : $i]:
% 6.64/6.85         (~ (v1_relat_1 @ X12)
% 6.64/6.85          | ~ (v1_funct_1 @ X12)
% 6.64/6.85          | ~ (r2_hidden @ X15 @ (k2_relat_1 @ X12))
% 6.64/6.85          | ((X15) = (k1_funct_1 @ X12 @ (sk_D_1 @ X15 @ X12))))),
% 6.64/6.85      inference('simplify', [status(thm)], ['73'])).
% 6.64/6.85  thf('75', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (((sk_C_1 @ k1_xboole_0 @ sk_C_2)
% 6.64/6.85            = (k1_funct_1 @ X0 @ 
% 6.64/6.85               (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ X0)))
% 6.64/6.85          | ~ (v1_funct_1 @ X0)
% 6.64/6.85          | ~ (v1_relat_1 @ X0))),
% 6.64/6.85      inference('sup-', [status(thm)], ['72', '74'])).
% 6.64/6.85  thf('76', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 6.64/6.85          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 6.64/6.85      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 6.64/6.85  thf('77', plain, (((sk_B) = (k1_xboole_0))),
% 6.64/6.85      inference('demod', [status(thm)], ['58', '61'])).
% 6.64/6.85  thf('78', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 6.64/6.85          | ((sk_C_1 @ k1_xboole_0 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 6.64/6.85      inference('demod', [status(thm)], ['76', '77'])).
% 6.64/6.85  thf('79', plain,
% 6.64/6.85      ((((sk_C_1 @ k1_xboole_0 @ sk_C_2) != (sk_C_1 @ k1_xboole_0 @ sk_C_2))
% 6.64/6.85        | ~ (v1_relat_1 @ sk_C_2)
% 6.64/6.85        | ~ (v1_funct_1 @ sk_C_2)
% 6.64/6.85        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ sk_C_2) @ 
% 6.64/6.85             (k1_relat_1 @ sk_C_2)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['75', '78'])).
% 6.64/6.85  thf('80', plain, ((v1_relat_1 @ sk_C_2)),
% 6.64/6.85      inference('demod', [status(thm)], ['15', '16'])).
% 6.64/6.85  thf('81', plain, ((v1_funct_1 @ sk_C_2)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('82', plain,
% 6.64/6.85      ((((sk_C_1 @ k1_xboole_0 @ sk_C_2) != (sk_C_1 @ k1_xboole_0 @ sk_C_2))
% 6.64/6.85        | ~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ sk_C_2) @ 
% 6.64/6.85             (k1_relat_1 @ sk_C_2)))),
% 6.64/6.85      inference('demod', [status(thm)], ['79', '80', '81'])).
% 6.64/6.85  thf('83', plain,
% 6.64/6.85      (~ (r2_hidden @ (sk_D_1 @ (sk_C_1 @ k1_xboole_0 @ sk_C_2) @ sk_C_2) @ 
% 6.64/6.85          (k1_relat_1 @ sk_C_2))),
% 6.64/6.85      inference('simplify', [status(thm)], ['82'])).
% 6.64/6.85  thf('84', plain, ((~ (v1_relat_1 @ sk_C_2) | ~ (v1_funct_1 @ sk_C_2))),
% 6.64/6.85      inference('sup-', [status(thm)], ['71', '83'])).
% 6.64/6.85  thf('85', plain, ((v1_relat_1 @ sk_C_2)),
% 6.64/6.85      inference('demod', [status(thm)], ['15', '16'])).
% 6.64/6.85  thf('86', plain, ((v1_funct_1 @ sk_C_2)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('87', plain, ($false),
% 6.64/6.85      inference('demod', [status(thm)], ['84', '85', '86'])).
% 6.64/6.85  
% 6.64/6.85  % SZS output end Refutation
% 6.64/6.85  
% 6.64/6.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
