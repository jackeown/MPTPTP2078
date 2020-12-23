%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0972+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o1Oz3wSFbT

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:48 EST 2020

% Result     : Theorem 3.87s
% Output     : Refutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  240 (63473 expanded)
%              Number of leaves         :   30 (18070 expanded)
%              Depth                    :   60
%              Number of atoms          : 2020 (1164566 expanded)
%              Number of equality atoms :  272 (65773 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference('sup+',[status(thm)],['26','42'])).

thf('44',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X20 )
        = ( k1_funct_1 @ sk_D @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_funct_1 @ X19 @ ( sk_C @ X18 @ X19 ) )
       != ( k1_funct_1 @ X18 @ ( sk_C @ X18 @ X19 ) ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('49',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference('sup-',[status(thm)],['13','55'])).

thf('57',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['63'])).

thf('65',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('67',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('70',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8 != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X10 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X9 @ k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('76',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('79',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('80',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('81',plain,
    ( ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('84',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,(
    ! [X3: $i] :
      ( zip_tseitin_0 @ X3 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['83','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['86'])).

thf('88',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','87'])).

thf('89',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('90',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('91',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('95',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('96',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('97',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['86'])).

thf('100',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('102',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('103',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('106',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('107',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('110',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('114',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = sk_D )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference('sup+',[status(thm)],['104','116'])).

thf('118',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X20: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X20 )
        = ( k1_funct_1 @ sk_D @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference(condensation,[status(thm)],['120'])).

thf('122',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_funct_1 @ X19 @ ( sk_C @ X18 @ X19 ) )
       != ( k1_funct_1 @ X18 @ ( sk_C @ X18 @ X19 ) ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('123',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('125',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('128',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference('sup-',[status(thm)],['92','129'])).

thf('131',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('133',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['0','66'])).

thf('135',plain,
    ( ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['62','64'])).

thf('137',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('138',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('140',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['67','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('143',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X9 @ k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('145',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','65'])).

thf('148',plain,(
    v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','148'])).

thf('150',plain,
    ( ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('151',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['86'])).

thf('153',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('155',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','148'])).

thf('157',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('158',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['86'])).

thf('160',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('162',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('164',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('166',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('167',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('170',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_D = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('173',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('174',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( sk_D = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172','173','174'])).

thf('176',plain,
    ( ( sk_A != sk_A )
    | ( sk_D = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( k1_xboole_0 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['165','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('178',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( sk_A != sk_A )
    | ( sk_D = k1_xboole_0 )
    | ( k1_xboole_0 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ k1_xboole_0 ) @ sk_A )
    | ( sk_D = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['164','180'])).

thf('182',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_D @ k1_xboole_0 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X20: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X20 )
        = ( k1_funct_1 @ sk_D @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('185',plain,(
    ! [X20: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ X20 )
        = ( k1_funct_1 @ sk_D @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ sk_D @ k1_xboole_0 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['182','185'])).

thf('187',plain,
    ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ sk_D @ k1_xboole_0 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['186'])).

thf('188',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_funct_1 @ X19 @ ( sk_C @ X18 @ X19 ) )
       != ( k1_funct_1 @ X18 @ ( sk_C @ X18 @ X19 ) ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('189',plain,
    ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ sk_D @ k1_xboole_0 ) )
     != ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ sk_D @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != ( k1_relat_1 @ sk_D ) )
    | ( k1_xboole_0 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('191',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('192',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('195',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('198',plain,
    ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ sk_D @ k1_xboole_0 ) )
     != ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ sk_D @ k1_xboole_0 ) ) )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != ( k1_relat_1 @ sk_D ) )
    | ( k1_xboole_0 = sk_D ) ),
    inference(demod,[status(thm)],['189','192','195','196','197'])).

thf('199',plain,
    ( ( k1_xboole_0 = sk_D )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != sk_A )
    | ( sk_D = k1_xboole_0 )
    | ( k1_xboole_0 = sk_D ) ),
    inference('sup-',[status(thm)],['155','199'])).

thf('201',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != sk_A ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('203',plain,(
    sk_D = k1_xboole_0 ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['136','137'])).

thf('205',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('206',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','138'])).

thf('207',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,(
    $false ),
    inference(demod,[status(thm)],['140','203','207'])).


%------------------------------------------------------------------------------
