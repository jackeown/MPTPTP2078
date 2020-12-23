%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y4CZYizLCN

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 845 expanded)
%              Number of leaves         :   49 ( 280 expanded)
%              Depth                    :   28
%              Number of atoms          :  981 (11104 expanded)
%              Number of equality atoms :   38 ( 211 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t191_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ C )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
             => ( ! [E: $i] :
                    ( ( m1_subset_1 @ E @ B )
                   => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
               => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
               => ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ B )
                     => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
                 => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('5',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( zip_tseitin_2 @ X42 @ X43 @ X44 @ X45 )
      | ( r2_hidden @ X42 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
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

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v5_relat_1 @ sk_D_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ( v5_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_C @ X1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( v5_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( v5_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('37',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['11','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','38','41'])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_2 @ D @ C @ B @ A ) )
       => ( zip_tseitin_3 @ C @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k1_relat_1 @ X50 )
       != X49 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X50 @ X51 @ X49 ) @ X50 @ X51 @ X49 )
      | ( zip_tseitin_3 @ X50 @ X51 @ X49 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('44',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ~ ( v1_funct_1 @ X50 )
      | ( zip_tseitin_3 @ X50 @ X51 @ ( k1_relat_1 @ X50 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X50 @ X51 @ ( k1_relat_1 @ X50 ) ) @ X50 @ X51 @ ( k1_relat_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','38','41'])).

thf('47',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','38','41'])).

thf('48',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','50'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('55',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( ( k3_funct_2 @ X39 @ X40 @ X38 @ X41 )
        = ( k1_funct_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('64',plain,(
    ! [X52: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X52 ) @ sk_A )
      | ~ ( m1_subset_1 @ X52 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( zip_tseitin_2 @ X42 @ X43 @ X44 @ X45 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X43 @ X42 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('71',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( zip_tseitin_3 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('74',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('76',plain,(
    v5_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('80',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['4','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y4CZYizLCN
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 180 iterations in 0.143s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.59  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.59  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.21/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.59  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.21/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.59  thf(t191_funct_2, conjecture,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.59       ( ![C:$i]:
% 0.21/0.59         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.59           ( ![D:$i]:
% 0.21/0.59             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.59                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.59               ( ( ![E:$i]:
% 0.21/0.59                   ( ( m1_subset_1 @ E @ B ) =>
% 0.21/0.59                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.21/0.59                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i,B:$i]:
% 0.21/0.59        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.59          ( ![C:$i]:
% 0.21/0.59            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.59              ( ![D:$i]:
% 0.21/0.59                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.59                    ( m1_subset_1 @
% 0.21/0.59                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.59                  ( ( ![E:$i]:
% 0.21/0.59                      ( ( m1_subset_1 @ E @ B ) =>
% 0.21/0.59                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.21/0.59                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.21/0.59  thf('0', plain,
% 0.21/0.59      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('1', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.59  thf('2', plain,
% 0.21/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.59         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.21/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.59  thf('3', plain,
% 0.21/0.59      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.59  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.21/0.59      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.59  thf(t5_funct_2, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.21/0.59       ( ( ( ![D:$i]:
% 0.21/0.59             ( ( r2_hidden @ D @ A ) =>
% 0.21/0.59               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.21/0.59           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.21/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.59           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_1, axiom,
% 0.21/0.59    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.59     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.21/0.59       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.21/0.59  thf('5', plain,
% 0.21/0.59      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.59         ((zip_tseitin_2 @ X42 @ X43 @ X44 @ X45) | (r2_hidden @ X42 @ X45))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.59  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(d1_funct_2, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_2, axiom,
% 0.21/0.59    (![C:$i,B:$i,A:$i]:
% 0.21/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.59  thf('7', plain,
% 0.21/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.59         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.21/0.59          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.21/0.59          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.59  thf('8', plain,
% 0.21/0.59      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.21/0.59        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.59  thf(zf_stmt_5, axiom,
% 0.21/0.59    (![B:$i,A:$i]:
% 0.21/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.59  thf(zf_stmt_6, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.59  thf('10', plain,
% 0.21/0.59      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.59         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.21/0.59          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.21/0.59          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.59  thf('11', plain,
% 0.21/0.59      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.21/0.59        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(cc2_relset_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.59  thf('13', plain,
% 0.21/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.59         ((v5_relat_1 @ X11 @ X13)
% 0.21/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.59  thf('14', plain, ((v5_relat_1 @ sk_D_1 @ sk_C)),
% 0.21/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.59  thf(d19_relat_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ B ) =>
% 0.21/0.59       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.59  thf('15', plain,
% 0.21/0.59      (![X6 : $i, X7 : $i]:
% 0.21/0.59         (~ (v5_relat_1 @ X6 @ X7)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.21/0.59          | ~ (v1_relat_1 @ X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.59  thf('16', plain,
% 0.21/0.59      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C))),
% 0.21/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.59  thf('17', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(cc1_relset_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.59       ( v1_relat_1 @ C ) ))).
% 0.21/0.59  thf('18', plain,
% 0.21/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.59         ((v1_relat_1 @ X8)
% 0.21/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.59  thf('19', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.59  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C)),
% 0.21/0.59      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.59  thf('21', plain,
% 0.21/0.59      (![X30 : $i, X31 : $i]:
% 0.21/0.59         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.59  thf('22', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.59  thf(d10_xboole_0, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.59  thf('23', plain,
% 0.21/0.59      (![X0 : $i, X2 : $i]:
% 0.21/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.59  thf('24', plain,
% 0.21/0.59      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.59  thf('25', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.59          | (zip_tseitin_0 @ X0 @ X2)
% 0.21/0.59          | ((X1) = (k1_xboole_0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.59  thf('26', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k2_relat_1 @ sk_D_1) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['20', '25'])).
% 0.21/0.59  thf('27', plain,
% 0.21/0.59      (![X6 : $i, X7 : $i]:
% 0.21/0.59         (~ (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.21/0.59          | (v5_relat_1 @ X6 @ X7)
% 0.21/0.59          | ~ (v1_relat_1 @ X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.59  thf('28', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.21/0.59          | (zip_tseitin_0 @ sk_C @ X1)
% 0.21/0.59          | ~ (v1_relat_1 @ sk_D_1)
% 0.21/0.59          | (v5_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.59  thf('29', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.59  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.59  thf('31', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((zip_tseitin_0 @ sk_C @ X1) | (v5_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.59  thf('32', plain,
% 0.21/0.59      (![X6 : $i, X7 : $i]:
% 0.21/0.59         (~ (v5_relat_1 @ X6 @ X7)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.21/0.59          | ~ (v1_relat_1 @ X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.59  thf('33', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((zip_tseitin_0 @ sk_C @ X1)
% 0.21/0.59          | ~ (v1_relat_1 @ sk_D_1)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.59  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.59  thf('35', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((zip_tseitin_0 @ sk_C @ X1)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 0.21/0.59      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.59  thf('36', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.21/0.59      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.59  thf('37', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.21/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.59  thf('38', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 0.21/0.59      inference('demod', [status(thm)], ['11', '37'])).
% 0.21/0.59  thf('39', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.59  thf('40', plain,
% 0.21/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.59         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.21/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.59  thf('41', plain,
% 0.21/0.59      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.59  thf('42', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.21/0.59      inference('demod', [status(thm)], ['8', '38', '41'])).
% 0.21/0.59  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.21/0.59  thf(zf_stmt_8, axiom,
% 0.21/0.59    (![C:$i,B:$i,A:$i]:
% 0.21/0.59     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 0.21/0.59       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.21/0.59  thf(zf_stmt_10, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.59       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.59           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 0.21/0.59         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 0.21/0.59  thf('43', plain,
% 0.21/0.59      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.21/0.59         (((k1_relat_1 @ X50) != (X49))
% 0.21/0.59          | ~ (zip_tseitin_2 @ (sk_D @ X50 @ X51 @ X49) @ X50 @ X51 @ X49)
% 0.21/0.59          | (zip_tseitin_3 @ X50 @ X51 @ X49)
% 0.21/0.59          | ~ (v1_funct_1 @ X50)
% 0.21/0.59          | ~ (v1_relat_1 @ X50))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.21/0.59  thf('44', plain,
% 0.21/0.59      (![X50 : $i, X51 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X50)
% 0.21/0.59          | ~ (v1_funct_1 @ X50)
% 0.21/0.59          | (zip_tseitin_3 @ X50 @ X51 @ (k1_relat_1 @ X50))
% 0.21/0.59          | ~ (zip_tseitin_2 @ (sk_D @ X50 @ X51 @ (k1_relat_1 @ X50)) @ X50 @ 
% 0.21/0.59               X51 @ (k1_relat_1 @ X50)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.59  thf('45', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 0.21/0.59             (k1_relat_1 @ sk_D_1))
% 0.21/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.21/0.59          | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.59          | ~ (v1_relat_1 @ sk_D_1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['42', '44'])).
% 0.21/0.59  thf('46', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.21/0.59      inference('demod', [status(thm)], ['8', '38', '41'])).
% 0.21/0.59  thf('47', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.21/0.59      inference('demod', [status(thm)], ['8', '38', '41'])).
% 0.21/0.59  thf('48', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('49', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.59  thf('50', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.21/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.21/0.59  thf('51', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 0.21/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['5', '50'])).
% 0.21/0.59  thf(t1_subset, axiom,
% 0.21/0.59    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.59  thf('52', plain,
% 0.21/0.59      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.59      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.59  thf('53', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.21/0.59          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.59  thf('54', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.59         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.59         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.59       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.59  thf('55', plain,
% 0.21/0.59      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.21/0.59         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.21/0.59          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.21/0.59          | ~ (v1_funct_1 @ X38)
% 0.21/0.59          | (v1_xboole_0 @ X39)
% 0.21/0.59          | ~ (m1_subset_1 @ X41 @ X39)
% 0.21/0.59          | ((k3_funct_2 @ X39 @ X40 @ X38 @ X41) = (k1_funct_1 @ X38 @ X41)))),
% 0.21/0.59      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.59  thf('56', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.21/0.59            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.21/0.59          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.59          | (v1_xboole_0 @ sk_B)
% 0.21/0.59          | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.59          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 0.21/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.59  thf('57', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('58', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('59', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.21/0.59            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.21/0.59          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.59          | (v1_xboole_0 @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.59  thf('60', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('61', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.59          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.21/0.59              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 0.21/0.59      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.59  thf('62', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.21/0.59          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 0.21/0.59              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 0.21/0.59      inference('sup-', [status(thm)], ['53', '61'])).
% 0.21/0.59  thf('63', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.21/0.59          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.59  thf('64', plain,
% 0.21/0.59      (![X52 : $i]:
% 0.21/0.59         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X52) @ sk_A)
% 0.21/0.59          | ~ (m1_subset_1 @ X52 @ sk_B))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('65', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.21/0.59          | (r2_hidden @ 
% 0.21/0.59             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.21/0.59             sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.59  thf('66', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.21/0.59           sk_A)
% 0.21/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.21/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.21/0.59      inference('sup+', [status(thm)], ['62', '65'])).
% 0.21/0.59  thf('67', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.21/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.21/0.59             sk_A))),
% 0.21/0.59      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.59  thf('68', plain,
% 0.21/0.59      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.59         ((zip_tseitin_2 @ X42 @ X43 @ X44 @ X45)
% 0.21/0.59          | ~ (r2_hidden @ (k1_funct_1 @ X43 @ X42) @ X44))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.59  thf('69', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.21/0.59          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.59  thf('70', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.21/0.59          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.21/0.59  thf('71', plain,
% 0.21/0.59      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 0.21/0.59        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.59  thf('72', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 0.21/0.59      inference('simplify', [status(thm)], ['71'])).
% 0.21/0.59  thf('73', plain,
% 0.21/0.59      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.21/0.59         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 0.21/0.59          | ~ (zip_tseitin_3 @ X46 @ X47 @ X48))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.21/0.59  thf('74', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.59  thf('75', plain,
% 0.21/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.59         ((v5_relat_1 @ X11 @ X13)
% 0.21/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.59  thf('76', plain, ((v5_relat_1 @ sk_D_1 @ sk_A)),
% 0.21/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.59  thf('77', plain,
% 0.21/0.59      (![X6 : $i, X7 : $i]:
% 0.21/0.59         (~ (v5_relat_1 @ X6 @ X7)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.21/0.59          | ~ (v1_relat_1 @ X6))),
% 0.21/0.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.59  thf('78', plain,
% 0.21/0.59      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A))),
% 0.21/0.59      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.59  thf('79', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.59  thf('80', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.21/0.59      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.59  thf('81', plain, ($false), inference('demod', [status(thm)], ['4', '80'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
