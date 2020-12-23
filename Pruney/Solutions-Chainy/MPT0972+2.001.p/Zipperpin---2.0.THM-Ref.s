%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FmwGdDUyYX

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:32 EST 2020

% Result     : Theorem 3.51s
% Output     : Refutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  227 (2931 expanded)
%              Number of leaves         :   45 ( 948 expanded)
%              Depth                    :   37
%              Number of atoms          : 1497 (24752 expanded)
%              Number of equality atoms :  107 (1283 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
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

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('14',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('28',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('29',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('36',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','42'])).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('45',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v4_relat_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('55',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('56',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('66',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('75',plain,(
    r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('77',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['63','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['44','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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

thf('83',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('84',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('88',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('91',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_B_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ X0 @ sk_C_2 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','97'])).

thf('99',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('104',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('107',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('109',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('115',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('118',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['113','120'])).

thf('122',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['100','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('124',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('126',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('131',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('133',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['122','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('136',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','136'])).

thf('138',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('139',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('141',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('142',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['140','142'])).

thf('144',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('145',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ),
    inference(clc,[status(thm)],['139','145'])).

thf('147',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','146'])).

thf('148',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['122','133'])).

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

thf('149',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('153',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['122','133'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['150','153','154','155'])).

thf('157',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['147','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('160',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['157','160','161'])).

thf('163',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X41: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X41 )
        = ( k1_funct_1 @ sk_D @ X41 ) )
      | ~ ( r2_hidden @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['165'])).

thf('167',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_funct_1 @ X19 @ ( sk_C_1 @ X18 @ X19 ) )
       != ( k1_funct_1 @ X18 @ ( sk_C_1 @ X18 @ X19 ) ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('168',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['151','152'])).

thf('170',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['122','133'])).

thf('172',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','146'])).

thf('173',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['158','159'])).

thf('175',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['168','169','170','171','172','173','174'])).

thf('176',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('179',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    $false ),
    inference(demod,[status(thm)],['0','176','179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FmwGdDUyYX
% 0.13/0.36  % Computer   : n015.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 17:33:23 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 3.51/3.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.51/3.76  % Solved by: fo/fo7.sh
% 3.51/3.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.51/3.76  % done 4264 iterations in 3.282s
% 3.51/3.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.51/3.76  % SZS output start Refutation
% 3.51/3.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.51/3.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.51/3.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.51/3.76  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 3.51/3.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.51/3.76  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.51/3.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.51/3.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.51/3.76  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.51/3.76  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.51/3.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.51/3.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.51/3.76  thf(sk_A_type, type, sk_A: $i).
% 3.51/3.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.51/3.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.51/3.76  thf(sk_D_type, type, sk_D: $i).
% 3.51/3.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.51/3.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.51/3.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.51/3.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.51/3.76  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.51/3.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.51/3.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.51/3.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.51/3.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.51/3.76  thf(t18_funct_2, conjecture,
% 3.51/3.76    (![A:$i,B:$i,C:$i]:
% 3.51/3.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.51/3.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.51/3.76       ( ![D:$i]:
% 3.51/3.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.51/3.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.51/3.76           ( ( ![E:$i]:
% 3.51/3.76               ( ( r2_hidden @ E @ A ) =>
% 3.51/3.76                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.51/3.76             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.51/3.76  thf(zf_stmt_0, negated_conjecture,
% 3.51/3.76    (~( ![A:$i,B:$i,C:$i]:
% 3.51/3.76        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.51/3.76            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.51/3.76          ( ![D:$i]:
% 3.51/3.76            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.51/3.76                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.51/3.76              ( ( ![E:$i]:
% 3.51/3.76                  ( ( r2_hidden @ E @ A ) =>
% 3.51/3.76                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.51/3.76                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.51/3.76    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 3.51/3.76  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_D)),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf(d1_funct_2, axiom,
% 3.51/3.76    (![A:$i,B:$i,C:$i]:
% 3.51/3.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.51/3.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.51/3.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.51/3.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.51/3.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.51/3.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.51/3.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.51/3.76  thf(zf_stmt_1, axiom,
% 3.51/3.76    (![C:$i,B:$i,A:$i]:
% 3.51/3.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.51/3.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.51/3.76  thf('2', plain,
% 3.51/3.76      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.51/3.76         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 3.51/3.76          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 3.51/3.76          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.51/3.76  thf('3', plain,
% 3.51/3.76      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 3.51/3.76        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['1', '2'])).
% 3.51/3.76  thf('4', plain,
% 3.51/3.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf(redefinition_k1_relset_1, axiom,
% 3.51/3.76    (![A:$i,B:$i,C:$i]:
% 3.51/3.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.51/3.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.51/3.76  thf('5', plain,
% 3.51/3.76      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.51/3.76         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 3.51/3.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.51/3.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.51/3.76  thf('6', plain,
% 3.51/3.76      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.51/3.76      inference('sup-', [status(thm)], ['4', '5'])).
% 3.51/3.76  thf('7', plain,
% 3.51/3.76      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 3.51/3.76        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.51/3.76      inference('demod', [status(thm)], ['3', '6'])).
% 3.51/3.76  thf(zf_stmt_2, axiom,
% 3.51/3.76    (![B:$i,A:$i]:
% 3.51/3.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.51/3.76       ( zip_tseitin_0 @ B @ A ) ))).
% 3.51/3.76  thf('8', plain,
% 3.51/3.76      (![X33 : $i, X34 : $i]:
% 3.51/3.76         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.51/3.76  thf(t113_zfmisc_1, axiom,
% 3.51/3.76    (![A:$i,B:$i]:
% 3.51/3.76     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.51/3.76       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.51/3.76  thf('9', plain,
% 3.51/3.76      (![X11 : $i, X12 : $i]:
% 3.51/3.76         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 3.51/3.76          | ((X12) != (k1_xboole_0)))),
% 3.51/3.76      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.51/3.76  thf('10', plain,
% 3.51/3.76      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.51/3.76      inference('simplify', [status(thm)], ['9'])).
% 3.51/3.76  thf('11', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.76         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.51/3.76      inference('sup+', [status(thm)], ['8', '10'])).
% 3.51/3.76  thf('12', plain,
% 3.51/3.76      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf(cc1_subset_1, axiom,
% 3.51/3.76    (![A:$i]:
% 3.51/3.76     ( ( v1_xboole_0 @ A ) =>
% 3.51/3.76       ( ![B:$i]:
% 3.51/3.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.51/3.76  thf('13', plain,
% 3.51/3.76      (![X14 : $i, X15 : $i]:
% 3.51/3.76         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.51/3.76          | (v1_xboole_0 @ X14)
% 3.51/3.76          | ~ (v1_xboole_0 @ X15))),
% 3.51/3.76      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.51/3.76  thf('14', plain,
% 3.51/3.76      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 3.51/3.76        | (v1_xboole_0 @ sk_C_2))),
% 3.51/3.76      inference('sup-', [status(thm)], ['12', '13'])).
% 3.51/3.76  thf('15', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.51/3.76          | (zip_tseitin_0 @ sk_B_2 @ X0)
% 3.51/3.76          | (v1_xboole_0 @ sk_C_2))),
% 3.51/3.76      inference('sup-', [status(thm)], ['11', '14'])).
% 3.51/3.76  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.51/3.76  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf('17', plain,
% 3.51/3.76      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 3.51/3.76      inference('demod', [status(thm)], ['15', '16'])).
% 3.51/3.76  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf(d3_tarski, axiom,
% 3.51/3.76    (![A:$i,B:$i]:
% 3.51/3.76     ( ( r1_tarski @ A @ B ) <=>
% 3.51/3.76       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.51/3.76  thf('19', plain,
% 3.51/3.76      (![X4 : $i, X6 : $i]:
% 3.51/3.76         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.51/3.76      inference('cnf', [status(esa)], [d3_tarski])).
% 3.51/3.76  thf(d1_xboole_0, axiom,
% 3.51/3.76    (![A:$i]:
% 3.51/3.76     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.51/3.76  thf('20', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.51/3.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.51/3.76  thf('21', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['19', '20'])).
% 3.51/3.76  thf('22', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['19', '20'])).
% 3.51/3.76  thf(d10_xboole_0, axiom,
% 3.51/3.76    (![A:$i,B:$i]:
% 3.51/3.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.51/3.76  thf('23', plain,
% 3.51/3.76      (![X7 : $i, X9 : $i]:
% 3.51/3.76         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.51/3.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.51/3.76  thf('24', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['22', '23'])).
% 3.51/3.76  thf('25', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['21', '24'])).
% 3.51/3.76  thf('26', plain,
% 3.51/3.76      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['18', '25'])).
% 3.51/3.76  thf('27', plain,
% 3.51/3.76      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['18', '25'])).
% 3.51/3.76  thf('28', plain,
% 3.51/3.76      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.51/3.76      inference('simplify', [status(thm)], ['9'])).
% 3.51/3.76  thf(existence_m1_subset_1, axiom,
% 3.51/3.76    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 3.51/3.76  thf('29', plain, (![X13 : $i]: (m1_subset_1 @ (sk_B_1 @ X13) @ X13)),
% 3.51/3.76      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 3.51/3.76  thf('30', plain,
% 3.51/3.76      (![X14 : $i, X15 : $i]:
% 3.51/3.76         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.51/3.76          | (v1_xboole_0 @ X14)
% 3.51/3.76          | ~ (v1_xboole_0 @ X15))),
% 3.51/3.76      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.51/3.76  thf('31', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (sk_B_1 @ (k1_zfmisc_1 @ X0))))),
% 3.51/3.76      inference('sup-', [status(thm)], ['29', '30'])).
% 3.51/3.76  thf('32', plain,
% 3.51/3.76      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['18', '25'])).
% 3.51/3.76  thf('33', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ X0)
% 3.51/3.76          | ((k1_xboole_0) = (sk_B_1 @ (k1_zfmisc_1 @ X0))))),
% 3.51/3.76      inference('sup-', [status(thm)], ['31', '32'])).
% 3.51/3.76  thf('34', plain, (![X13 : $i]: (m1_subset_1 @ (sk_B_1 @ X13) @ X13)),
% 3.51/3.76      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 3.51/3.76  thf('35', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 3.51/3.76          | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup+', [status(thm)], ['33', '34'])).
% 3.51/3.76  thf(reflexivity_r2_relset_1, axiom,
% 3.51/3.76    (![A:$i,B:$i,C:$i,D:$i]:
% 3.51/3.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.51/3.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.51/3.76       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 3.51/3.76  thf('36', plain,
% 3.51/3.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.51/3.76         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 3.51/3.76          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.51/3.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 3.51/3.76      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 3.51/3.76  thf('37', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.76         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.51/3.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.51/3.76      inference('condensation', [status(thm)], ['36'])).
% 3.51/3.76  thf('38', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.51/3.76          | (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['35', '37'])).
% 3.51/3.76  thf('39', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.51/3.76          | (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['28', '38'])).
% 3.51/3.76  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf('41', plain,
% 3.51/3.76      (![X0 : $i]: (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('demod', [status(thm)], ['39', '40'])).
% 3.51/3.76  thf('42', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]:
% 3.51/3.76         ((r2_relset_1 @ X1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 3.51/3.76          | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup+', [status(thm)], ['27', '41'])).
% 3.51/3.76  thf('43', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.76         ((r2_relset_1 @ X2 @ k1_xboole_0 @ X1 @ X0)
% 3.51/3.76          | ~ (v1_xboole_0 @ X0)
% 3.51/3.76          | ~ (v1_xboole_0 @ X1))),
% 3.51/3.76      inference('sup+', [status(thm)], ['26', '42'])).
% 3.51/3.76  thf('44', plain,
% 3.51/3.76      (![X33 : $i, X34 : $i]:
% 3.51/3.76         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.51/3.76  thf('45', plain,
% 3.51/3.76      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.51/3.76      inference('simplify', [status(thm)], ['9'])).
% 3.51/3.76  thf('46', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 3.51/3.76          | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup+', [status(thm)], ['33', '34'])).
% 3.51/3.76  thf(cc2_relset_1, axiom,
% 3.51/3.76    (![A:$i,B:$i,C:$i]:
% 3.51/3.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.51/3.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.51/3.76  thf('47', plain,
% 3.51/3.76      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.51/3.76         ((v4_relat_1 @ X23 @ X24)
% 3.51/3.76          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.51/3.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.51/3.76  thf('48', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.51/3.76          | (v4_relat_1 @ k1_xboole_0 @ X1))),
% 3.51/3.76      inference('sup-', [status(thm)], ['46', '47'])).
% 3.51/3.76  thf('49', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ k1_xboole_0) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['45', '48'])).
% 3.51/3.76  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf('51', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 3.51/3.76      inference('demod', [status(thm)], ['49', '50'])).
% 3.51/3.76  thf(d18_relat_1, axiom,
% 3.51/3.76    (![A:$i,B:$i]:
% 3.51/3.76     ( ( v1_relat_1 @ B ) =>
% 3.51/3.76       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.51/3.76  thf('52', plain,
% 3.51/3.76      (![X16 : $i, X17 : $i]:
% 3.51/3.76         (~ (v4_relat_1 @ X16 @ X17)
% 3.51/3.76          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 3.51/3.76          | ~ (v1_relat_1 @ X16))),
% 3.51/3.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.51/3.76  thf('53', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (~ (v1_relat_1 @ k1_xboole_0)
% 3.51/3.76          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['51', '52'])).
% 3.51/3.76  thf('54', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ X0)
% 3.51/3.76          | ((k1_xboole_0) = (sk_B_1 @ (k1_zfmisc_1 @ X0))))),
% 3.51/3.76      inference('sup-', [status(thm)], ['31', '32'])).
% 3.51/3.76  thf('55', plain, (![X13 : $i]: (m1_subset_1 @ (sk_B_1 @ X13) @ X13)),
% 3.51/3.76      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 3.51/3.76  thf('56', plain,
% 3.51/3.76      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 3.51/3.76      inference('simplify', [status(thm)], ['9'])).
% 3.51/3.76  thf(cc1_relset_1, axiom,
% 3.51/3.76    (![A:$i,B:$i,C:$i]:
% 3.51/3.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.51/3.76       ( v1_relat_1 @ C ) ))).
% 3.51/3.76  thf('57', plain,
% 3.51/3.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.51/3.76         ((v1_relat_1 @ X20)
% 3.51/3.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.51/3.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.51/3.76  thf('58', plain,
% 3.51/3.76      (![X1 : $i]:
% 3.51/3.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.51/3.76          | (v1_relat_1 @ X1))),
% 3.51/3.76      inference('sup-', [status(thm)], ['56', '57'])).
% 3.51/3.76  thf('59', plain, ((v1_relat_1 @ (sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['55', '58'])).
% 3.51/3.76  thf('60', plain,
% 3.51/3.76      (((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.51/3.76      inference('sup+', [status(thm)], ['54', '59'])).
% 3.51/3.76  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf('62', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.51/3.76      inference('demod', [status(thm)], ['60', '61'])).
% 3.51/3.76  thf('63', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 3.51/3.76      inference('demod', [status(thm)], ['53', '62'])).
% 3.51/3.76  thf('64', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 3.51/3.76          | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup+', [status(thm)], ['33', '34'])).
% 3.51/3.76  thf('65', plain,
% 3.51/3.76      (![X11 : $i, X12 : $i]:
% 3.51/3.76         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 3.51/3.76          | ((X11) != (k1_xboole_0)))),
% 3.51/3.76      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.51/3.76  thf('66', plain,
% 3.51/3.76      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 3.51/3.76      inference('simplify', [status(thm)], ['65'])).
% 3.51/3.76  thf('67', plain,
% 3.51/3.76      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.51/3.76         ((v4_relat_1 @ X23 @ X24)
% 3.51/3.76          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.51/3.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.51/3.76  thf('68', plain,
% 3.51/3.76      (![X1 : $i]:
% 3.51/3.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.51/3.76          | (v4_relat_1 @ X1 @ k1_xboole_0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['66', '67'])).
% 3.51/3.76  thf('69', plain,
% 3.51/3.76      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.51/3.76        | (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['64', '68'])).
% 3.51/3.76  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf('71', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('demod', [status(thm)], ['69', '70'])).
% 3.51/3.76  thf('72', plain,
% 3.51/3.76      (![X16 : $i, X17 : $i]:
% 3.51/3.76         (~ (v4_relat_1 @ X16 @ X17)
% 3.51/3.76          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 3.51/3.76          | ~ (v1_relat_1 @ X16))),
% 3.51/3.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.51/3.76  thf('73', plain,
% 3.51/3.76      ((~ (v1_relat_1 @ k1_xboole_0)
% 3.51/3.76        | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['71', '72'])).
% 3.51/3.76  thf('74', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.51/3.76      inference('demod', [status(thm)], ['60', '61'])).
% 3.51/3.76  thf('75', plain, ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 3.51/3.76      inference('demod', [status(thm)], ['73', '74'])).
% 3.51/3.76  thf('76', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['22', '23'])).
% 3.51/3.76  thf('77', plain,
% 3.51/3.76      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 3.51/3.76        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['75', '76'])).
% 3.51/3.76  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf('79', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.51/3.76      inference('demod', [status(thm)], ['77', '78'])).
% 3.51/3.76  thf('80', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.51/3.76      inference('demod', [status(thm)], ['63', '79'])).
% 3.51/3.76  thf('81', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.76         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 3.51/3.76      inference('sup+', [status(thm)], ['44', '80'])).
% 3.51/3.76  thf('82', plain,
% 3.51/3.76      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.51/3.76  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.51/3.76  thf(zf_stmt_5, axiom,
% 3.51/3.76    (![A:$i,B:$i,C:$i]:
% 3.51/3.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.51/3.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.51/3.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.51/3.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.51/3.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.51/3.76  thf('83', plain,
% 3.51/3.76      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.51/3.76         (~ (zip_tseitin_0 @ X38 @ X39)
% 3.51/3.76          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 3.51/3.76          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.51/3.76  thf('84', plain,
% 3.51/3.76      (((zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)
% 3.51/3.76        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['82', '83'])).
% 3.51/3.76  thf('85', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         ((r1_tarski @ sk_B_2 @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['81', '84'])).
% 3.51/3.76  thf('86', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2)),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('87', plain,
% 3.51/3.76      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.51/3.76         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 3.51/3.76          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 3.51/3.76          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.51/3.76  thf('88', plain,
% 3.51/3.76      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)
% 3.51/3.76        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['86', '87'])).
% 3.51/3.76  thf('89', plain,
% 3.51/3.76      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('90', plain,
% 3.51/3.76      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.51/3.76         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 3.51/3.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 3.51/3.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.51/3.76  thf('91', plain,
% 3.51/3.76      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.51/3.76      inference('sup-', [status(thm)], ['89', '90'])).
% 3.51/3.76  thf('92', plain,
% 3.51/3.76      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)
% 3.51/3.76        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.51/3.76      inference('demod', [status(thm)], ['88', '91'])).
% 3.51/3.76  thf('93', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         ((r1_tarski @ sk_B_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['85', '92'])).
% 3.51/3.76  thf('94', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['22', '23'])).
% 3.51/3.76  thf('95', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 3.51/3.76          | ((sk_B_2) = (X0))
% 3.51/3.76          | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['93', '94'])).
% 3.51/3.76  thf('96', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_D)),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('97', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (~ (r2_relset_1 @ sk_A @ X0 @ sk_C_2 @ sk_D)
% 3.51/3.76          | ~ (v1_xboole_0 @ X0)
% 3.51/3.76          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['95', '96'])).
% 3.51/3.76  thf('98', plain,
% 3.51/3.76      ((~ (v1_xboole_0 @ sk_C_2)
% 3.51/3.76        | ~ (v1_xboole_0 @ sk_D)
% 3.51/3.76        | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 3.51/3.76        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['43', '97'])).
% 3.51/3.76  thf('99', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf('100', plain,
% 3.51/3.76      ((~ (v1_xboole_0 @ sk_C_2)
% 3.51/3.76        | ~ (v1_xboole_0 @ sk_D)
% 3.51/3.76        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.51/3.76      inference('demod', [status(thm)], ['98', '99'])).
% 3.51/3.76  thf('101', plain,
% 3.51/3.76      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 3.51/3.76      inference('demod', [status(thm)], ['15', '16'])).
% 3.51/3.76  thf('102', plain,
% 3.51/3.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('103', plain,
% 3.51/3.76      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.51/3.76         (~ (zip_tseitin_0 @ X38 @ X39)
% 3.51/3.76          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 3.51/3.76          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.51/3.76  thf('104', plain,
% 3.51/3.76      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 3.51/3.76        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['102', '103'])).
% 3.51/3.76  thf('105', plain,
% 3.51/3.76      (((v1_xboole_0 @ sk_C_2) | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['101', '104'])).
% 3.51/3.76  thf('106', plain,
% 3.51/3.76      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 3.51/3.76        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.51/3.76      inference('demod', [status(thm)], ['3', '6'])).
% 3.51/3.76  thf('107', plain,
% 3.51/3.76      (((v1_xboole_0 @ sk_C_2) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['105', '106'])).
% 3.51/3.76  thf('108', plain,
% 3.51/3.76      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['18', '25'])).
% 3.51/3.76  thf('109', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.51/3.76      inference('demod', [status(thm)], ['77', '78'])).
% 3.51/3.76  thf('110', plain,
% 3.51/3.76      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup+', [status(thm)], ['108', '109'])).
% 3.51/3.76  thf('111', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf('112', plain,
% 3.51/3.76      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup+', [status(thm)], ['110', '111'])).
% 3.51/3.76  thf('113', plain,
% 3.51/3.76      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 3.51/3.76      inference('sup+', [status(thm)], ['107', '112'])).
% 3.51/3.76  thf('114', plain,
% 3.51/3.76      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['18', '25'])).
% 3.51/3.76  thf('115', plain,
% 3.51/3.76      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 3.51/3.76      inference('simplify', [status(thm)], ['65'])).
% 3.51/3.76  thf('116', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]:
% 3.51/3.76         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup+', [status(thm)], ['114', '115'])).
% 3.51/3.76  thf('117', plain,
% 3.51/3.76      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 3.51/3.76        | (v1_xboole_0 @ sk_C_2))),
% 3.51/3.76      inference('sup-', [status(thm)], ['12', '13'])).
% 3.51/3.76  thf('118', plain,
% 3.51/3.76      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.51/3.76        | ~ (v1_xboole_0 @ sk_A)
% 3.51/3.76        | (v1_xboole_0 @ sk_C_2))),
% 3.51/3.76      inference('sup-', [status(thm)], ['116', '117'])).
% 3.51/3.76  thf('119', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf('120', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_2))),
% 3.51/3.76      inference('demod', [status(thm)], ['118', '119'])).
% 3.51/3.76  thf('121', plain, ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C_2))),
% 3.51/3.76      inference('clc', [status(thm)], ['113', '120'])).
% 3.51/3.76  thf('122', plain,
% 3.51/3.76      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_D))),
% 3.51/3.76      inference('clc', [status(thm)], ['100', '121'])).
% 3.51/3.76  thf('123', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.76         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.51/3.76      inference('sup+', [status(thm)], ['8', '10'])).
% 3.51/3.76  thf('124', plain,
% 3.51/3.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('125', plain,
% 3.51/3.76      (![X14 : $i, X15 : $i]:
% 3.51/3.76         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 3.51/3.76          | (v1_xboole_0 @ X14)
% 3.51/3.76          | ~ (v1_xboole_0 @ X15))),
% 3.51/3.76      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.51/3.76  thf('126', plain,
% 3.51/3.76      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | (v1_xboole_0 @ sk_D))),
% 3.51/3.76      inference('sup-', [status(thm)], ['124', '125'])).
% 3.51/3.76  thf('127', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.51/3.76          | (zip_tseitin_0 @ sk_B_2 @ X0)
% 3.51/3.76          | (v1_xboole_0 @ sk_D))),
% 3.51/3.76      inference('sup-', [status(thm)], ['123', '126'])).
% 3.51/3.76  thf('128', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.51/3.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.51/3.76  thf('129', plain,
% 3.51/3.76      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | (v1_xboole_0 @ sk_D))),
% 3.51/3.76      inference('demod', [status(thm)], ['127', '128'])).
% 3.51/3.76  thf('130', plain,
% 3.51/3.76      (((zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)
% 3.51/3.76        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['82', '83'])).
% 3.51/3.76  thf('131', plain,
% 3.51/3.76      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['129', '130'])).
% 3.51/3.76  thf('132', plain,
% 3.51/3.76      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)
% 3.51/3.76        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.51/3.76      inference('demod', [status(thm)], ['88', '91'])).
% 3.51/3.76  thf('133', plain,
% 3.51/3.76      (((v1_xboole_0 @ sk_D) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['131', '132'])).
% 3.51/3.76  thf('134', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.51/3.76      inference('clc', [status(thm)], ['122', '133'])).
% 3.51/3.76  thf('135', plain,
% 3.51/3.76      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup+', [status(thm)], ['110', '111'])).
% 3.51/3.76  thf('136', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C_2))),
% 3.51/3.76      inference('sup+', [status(thm)], ['134', '135'])).
% 3.51/3.76  thf('137', plain,
% 3.51/3.76      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | (v1_xboole_0 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['17', '136'])).
% 3.51/3.76  thf('138', plain,
% 3.51/3.76      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 3.51/3.76        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['102', '103'])).
% 3.51/3.76  thf('139', plain,
% 3.51/3.76      (((v1_xboole_0 @ sk_A) | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['137', '138'])).
% 3.51/3.76  thf('140', plain,
% 3.51/3.76      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['18', '25'])).
% 3.51/3.76  thf('141', plain,
% 3.51/3.76      (![X33 : $i, X34 : $i]:
% 3.51/3.76         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.51/3.76  thf('142', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 3.51/3.76      inference('simplify', [status(thm)], ['141'])).
% 3.51/3.76  thf('143', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.51/3.76      inference('sup+', [status(thm)], ['140', '142'])).
% 3.51/3.76  thf('144', plain,
% 3.51/3.76      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 3.51/3.76        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['102', '103'])).
% 3.51/3.76  thf('145', plain,
% 3.51/3.76      ((~ (v1_xboole_0 @ sk_A) | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['143', '144'])).
% 3.51/3.76  thf('146', plain, ((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)),
% 3.51/3.76      inference('clc', [status(thm)], ['139', '145'])).
% 3.51/3.76  thf('147', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.51/3.76      inference('demod', [status(thm)], ['7', '146'])).
% 3.51/3.76  thf('148', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.51/3.76      inference('clc', [status(thm)], ['122', '133'])).
% 3.51/3.76  thf(t9_funct_1, axiom,
% 3.51/3.76    (![A:$i]:
% 3.51/3.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.51/3.76       ( ![B:$i]:
% 3.51/3.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.51/3.76           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.51/3.76               ( ![C:$i]:
% 3.51/3.76                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.51/3.76                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.51/3.76             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.51/3.76  thf('149', plain,
% 3.51/3.76      (![X18 : $i, X19 : $i]:
% 3.51/3.76         (~ (v1_relat_1 @ X18)
% 3.51/3.76          | ~ (v1_funct_1 @ X18)
% 3.51/3.76          | ((X19) = (X18))
% 3.51/3.76          | (r2_hidden @ (sk_C_1 @ X18 @ X19) @ (k1_relat_1 @ X19))
% 3.51/3.76          | ((k1_relat_1 @ X19) != (k1_relat_1 @ X18))
% 3.51/3.76          | ~ (v1_funct_1 @ X19)
% 3.51/3.76          | ~ (v1_relat_1 @ X19))),
% 3.51/3.76      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.51/3.76  thf('150', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (((sk_A) != (k1_relat_1 @ X0))
% 3.51/3.76          | ~ (v1_relat_1 @ sk_C_2)
% 3.51/3.76          | ~ (v1_funct_1 @ sk_C_2)
% 3.51/3.76          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 3.51/3.76          | ((sk_C_2) = (X0))
% 3.51/3.76          | ~ (v1_funct_1 @ X0)
% 3.51/3.76          | ~ (v1_relat_1 @ X0))),
% 3.51/3.76      inference('sup-', [status(thm)], ['148', '149'])).
% 3.51/3.76  thf('151', plain,
% 3.51/3.76      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('152', plain,
% 3.51/3.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.51/3.76         ((v1_relat_1 @ X20)
% 3.51/3.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.51/3.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.51/3.76  thf('153', plain, ((v1_relat_1 @ sk_C_2)),
% 3.51/3.76      inference('sup-', [status(thm)], ['151', '152'])).
% 3.51/3.76  thf('154', plain, ((v1_funct_1 @ sk_C_2)),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('155', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.51/3.76      inference('clc', [status(thm)], ['122', '133'])).
% 3.51/3.76  thf('156', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (((sk_A) != (k1_relat_1 @ X0))
% 3.51/3.76          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 3.51/3.76          | ((sk_C_2) = (X0))
% 3.51/3.76          | ~ (v1_funct_1 @ X0)
% 3.51/3.76          | ~ (v1_relat_1 @ X0))),
% 3.51/3.76      inference('demod', [status(thm)], ['150', '153', '154', '155'])).
% 3.51/3.76  thf('157', plain,
% 3.51/3.76      ((((sk_A) != (sk_A))
% 3.51/3.76        | ~ (v1_relat_1 @ sk_D)
% 3.51/3.76        | ~ (v1_funct_1 @ sk_D)
% 3.51/3.76        | ((sk_C_2) = (sk_D))
% 3.51/3.76        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.51/3.76      inference('sup-', [status(thm)], ['147', '156'])).
% 3.51/3.76  thf('158', plain,
% 3.51/3.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('159', plain,
% 3.51/3.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.51/3.76         ((v1_relat_1 @ X20)
% 3.51/3.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.51/3.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.51/3.76  thf('160', plain, ((v1_relat_1 @ sk_D)),
% 3.51/3.76      inference('sup-', [status(thm)], ['158', '159'])).
% 3.51/3.76  thf('161', plain, ((v1_funct_1 @ sk_D)),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('162', plain,
% 3.51/3.76      ((((sk_A) != (sk_A))
% 3.51/3.76        | ((sk_C_2) = (sk_D))
% 3.51/3.76        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.51/3.76      inference('demod', [status(thm)], ['157', '160', '161'])).
% 3.51/3.76  thf('163', plain,
% 3.51/3.76      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 3.51/3.76      inference('simplify', [status(thm)], ['162'])).
% 3.51/3.76  thf('164', plain,
% 3.51/3.76      (![X41 : $i]:
% 3.51/3.76         (((k1_funct_1 @ sk_C_2 @ X41) = (k1_funct_1 @ sk_D @ X41))
% 3.51/3.76          | ~ (r2_hidden @ X41 @ sk_A))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('165', plain,
% 3.51/3.76      ((((sk_C_2) = (sk_D))
% 3.51/3.76        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.51/3.76            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 3.51/3.76      inference('sup-', [status(thm)], ['163', '164'])).
% 3.51/3.76  thf('166', plain,
% 3.51/3.76      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.51/3.76         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 3.51/3.76      inference('condensation', [status(thm)], ['165'])).
% 3.51/3.76  thf('167', plain,
% 3.51/3.76      (![X18 : $i, X19 : $i]:
% 3.51/3.76         (~ (v1_relat_1 @ X18)
% 3.51/3.76          | ~ (v1_funct_1 @ X18)
% 3.51/3.76          | ((X19) = (X18))
% 3.51/3.76          | ((k1_funct_1 @ X19 @ (sk_C_1 @ X18 @ X19))
% 3.51/3.76              != (k1_funct_1 @ X18 @ (sk_C_1 @ X18 @ X19)))
% 3.51/3.76          | ((k1_relat_1 @ X19) != (k1_relat_1 @ X18))
% 3.51/3.76          | ~ (v1_funct_1 @ X19)
% 3.51/3.76          | ~ (v1_relat_1 @ X19))),
% 3.51/3.76      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.51/3.76  thf('168', plain,
% 3.51/3.76      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.51/3.76          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.51/3.76        | ~ (v1_relat_1 @ sk_C_2)
% 3.51/3.76        | ~ (v1_funct_1 @ sk_C_2)
% 3.51/3.76        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 3.51/3.76        | ((sk_C_2) = (sk_D))
% 3.51/3.76        | ~ (v1_funct_1 @ sk_D)
% 3.51/3.76        | ~ (v1_relat_1 @ sk_D))),
% 3.51/3.76      inference('sup-', [status(thm)], ['166', '167'])).
% 3.51/3.76  thf('169', plain, ((v1_relat_1 @ sk_C_2)),
% 3.51/3.76      inference('sup-', [status(thm)], ['151', '152'])).
% 3.51/3.76  thf('170', plain, ((v1_funct_1 @ sk_C_2)),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('171', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.51/3.76      inference('clc', [status(thm)], ['122', '133'])).
% 3.51/3.76  thf('172', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.51/3.76      inference('demod', [status(thm)], ['7', '146'])).
% 3.51/3.76  thf('173', plain, ((v1_funct_1 @ sk_D)),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('174', plain, ((v1_relat_1 @ sk_D)),
% 3.51/3.76      inference('sup-', [status(thm)], ['158', '159'])).
% 3.51/3.76  thf('175', plain,
% 3.51/3.76      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.51/3.76          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.51/3.76        | ((sk_A) != (sk_A))
% 3.51/3.76        | ((sk_C_2) = (sk_D)))),
% 3.51/3.76      inference('demod', [status(thm)],
% 3.51/3.76                ['168', '169', '170', '171', '172', '173', '174'])).
% 3.51/3.76  thf('176', plain, (((sk_C_2) = (sk_D))),
% 3.51/3.76      inference('simplify', [status(thm)], ['175'])).
% 3.51/3.76  thf('177', plain,
% 3.51/3.76      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('178', plain,
% 3.51/3.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.51/3.76         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.51/3.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.51/3.76      inference('condensation', [status(thm)], ['36'])).
% 3.51/3.76  thf('179', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 @ sk_C_2)),
% 3.51/3.76      inference('sup-', [status(thm)], ['177', '178'])).
% 3.51/3.76  thf('180', plain, ($false),
% 3.51/3.76      inference('demod', [status(thm)], ['0', '176', '179'])).
% 3.51/3.76  
% 3.51/3.76  % SZS output end Refutation
% 3.51/3.76  
% 3.61/3.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
