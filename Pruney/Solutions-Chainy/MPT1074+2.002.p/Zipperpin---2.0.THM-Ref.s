%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hVvp2OqK08

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:22 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 665 expanded)
%              Number of leaves         :   48 ( 217 expanded)
%              Depth                    :   25
%              Number of atoms          :  945 (9142 expanded)
%              Number of equality atoms :   43 ( 283 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( zip_tseitin_2 @ X43 @ X44 @ X45 @ X46 )
      | ( r2_hidden @ X43 @ X46 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( v5_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('30',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['11','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','31','34'])).

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

thf('36',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k1_relat_1 @ X51 )
       != X50 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X51 @ X52 @ X50 ) @ X51 @ X52 @ X50 )
      | ( zip_tseitin_3 @ X51 @ X52 @ X50 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('37',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ~ ( v1_funct_1 @ X51 )
      | ( zip_tseitin_3 @ X51 @ X52 @ ( k1_relat_1 @ X51 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X51 @ X52 @ ( k1_relat_1 @ X51 ) ) @ X51 @ X52 @ ( k1_relat_1 @ X51 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','31','34'])).

thf('40',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','31','34'])).

thf('41',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','43'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( ( k3_funct_2 @ X39 @ X40 @ X38 @ X41 )
        = ( k1_funct_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('57',plain,(
    ! [X53: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X53 ) @ sk_A )
      | ~ ( m1_subset_1 @ X53 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( zip_tseitin_2 @ X43 @ X44 @ X45 @ X46 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X44 @ X43 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('64',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( zip_tseitin_3 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('67',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('69',plain,(
    v5_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('73',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['4','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hVvp2OqK08
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.03  % Solved by: fo/fo7.sh
% 0.82/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.03  % done 627 iterations in 0.577s
% 0.82/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.03  % SZS output start Refutation
% 0.82/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.03  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.82/1.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.82/1.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.82/1.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.82/1.03  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.82/1.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.82/1.03  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.82/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.82/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.03  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.82/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.82/1.03  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.82/1.03  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.82/1.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.82/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.82/1.03  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.82/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.82/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.82/1.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.82/1.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.82/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.03  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.82/1.03  thf(t191_funct_2, conjecture,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.82/1.03       ( ![C:$i]:
% 0.82/1.03         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.82/1.03           ( ![D:$i]:
% 0.82/1.03             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.82/1.03                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.82/1.03               ( ( ![E:$i]:
% 0.82/1.03                   ( ( m1_subset_1 @ E @ B ) =>
% 0.82/1.03                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.82/1.03                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.82/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.03    (~( ![A:$i,B:$i]:
% 0.82/1.03        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.82/1.03          ( ![C:$i]:
% 0.82/1.03            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.82/1.03              ( ![D:$i]:
% 0.82/1.03                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.82/1.03                    ( m1_subset_1 @
% 0.82/1.03                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.82/1.03                  ( ( ![E:$i]:
% 0.82/1.03                      ( ( m1_subset_1 @ E @ B ) =>
% 0.82/1.03                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.82/1.03                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.82/1.03    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.82/1.03  thf('0', plain,
% 0.82/1.03      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('1', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(redefinition_k2_relset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.03       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.82/1.03  thf('2', plain,
% 0.82/1.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.82/1.03         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.82/1.03          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.82/1.03  thf('3', plain,
% 0.82/1.03      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.82/1.03  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.82/1.03      inference('demod', [status(thm)], ['0', '3'])).
% 0.82/1.03  thf(t5_funct_2, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.82/1.03       ( ( ( ![D:$i]:
% 0.82/1.03             ( ( r2_hidden @ D @ A ) =>
% 0.82/1.03               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.82/1.03           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.82/1.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.82/1.03           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.82/1.03  thf(zf_stmt_1, axiom,
% 0.82/1.03    (![D:$i,C:$i,B:$i,A:$i]:
% 0.82/1.03     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.82/1.03       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.82/1.03  thf('5', plain,
% 0.82/1.03      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.82/1.03         ((zip_tseitin_2 @ X43 @ X44 @ X45 @ X46) | (r2_hidden @ X43 @ X46))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.03  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(d1_funct_2, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.03       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.82/1.03           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.82/1.03             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.82/1.03         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.82/1.03           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.82/1.03             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.82/1.03  thf(zf_stmt_2, axiom,
% 0.82/1.03    (![C:$i,B:$i,A:$i]:
% 0.82/1.03     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.82/1.03       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.82/1.03  thf('7', plain,
% 0.82/1.03      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.82/1.03         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.82/1.03          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.82/1.03          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.03  thf('8', plain,
% 0.82/1.03      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.82/1.03        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.82/1.03  thf('9', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.82/1.03  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.82/1.03  thf(zf_stmt_5, axiom,
% 0.82/1.03    (![B:$i,A:$i]:
% 0.82/1.03     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.82/1.03       ( zip_tseitin_0 @ B @ A ) ))).
% 0.82/1.03  thf(zf_stmt_6, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.03       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.82/1.03         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.82/1.03           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.82/1.03  thf('10', plain,
% 0.82/1.03      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.82/1.03         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.82/1.03          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.82/1.03          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.82/1.03  thf('11', plain,
% 0.82/1.03      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.82/1.03        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.82/1.03  thf('12', plain,
% 0.82/1.03      (![X30 : $i, X31 : $i]:
% 0.82/1.03         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.82/1.03  thf(t113_zfmisc_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.82/1.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.82/1.03  thf('13', plain,
% 0.82/1.03      (![X1 : $i, X2 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.82/1.03  thf('14', plain,
% 0.82/1.03      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['13'])).
% 0.82/1.03  thf('15', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.82/1.03      inference('sup+', [status(thm)], ['12', '14'])).
% 0.82/1.03  thf('16', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('17', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.82/1.03          | (zip_tseitin_0 @ sk_C @ X0))),
% 0.82/1.03      inference('sup+', [status(thm)], ['15', '16'])).
% 0.82/1.03  thf('18', plain,
% 0.82/1.03      (![X1 : $i, X2 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.82/1.03  thf('19', plain,
% 0.82/1.03      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['18'])).
% 0.82/1.03  thf(cc2_relset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.03       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.82/1.03  thf('20', plain,
% 0.82/1.03      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.82/1.03         ((v5_relat_1 @ X12 @ X14)
% 0.82/1.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.82/1.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.82/1.03  thf('21', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.82/1.03          | (v5_relat_1 @ X1 @ X0))),
% 0.82/1.03      inference('sup-', [status(thm)], ['19', '20'])).
% 0.82/1.03  thf('22', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         ((zip_tseitin_0 @ sk_C @ X1) | (v5_relat_1 @ sk_D_1 @ X0))),
% 0.82/1.03      inference('sup-', [status(thm)], ['17', '21'])).
% 0.82/1.03  thf(d19_relat_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( v1_relat_1 @ B ) =>
% 0.82/1.03       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.82/1.03  thf('23', plain,
% 0.82/1.03      (![X7 : $i, X8 : $i]:
% 0.82/1.03         (~ (v5_relat_1 @ X7 @ X8)
% 0.82/1.03          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.82/1.03          | ~ (v1_relat_1 @ X7))),
% 0.82/1.03      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.82/1.03  thf('24', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         ((zip_tseitin_0 @ sk_C @ X1)
% 0.82/1.03          | ~ (v1_relat_1 @ sk_D_1)
% 0.82/1.03          | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 0.82/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.82/1.03  thf('25', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(cc1_relset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.03       ( v1_relat_1 @ C ) ))).
% 0.82/1.03  thf('26', plain,
% 0.82/1.03      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.82/1.03         ((v1_relat_1 @ X9)
% 0.82/1.03          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.82/1.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.82/1.03  thf('27', plain, ((v1_relat_1 @ sk_D_1)),
% 0.82/1.03      inference('sup-', [status(thm)], ['25', '26'])).
% 0.82/1.03  thf('28', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         ((zip_tseitin_0 @ sk_C @ X1)
% 0.82/1.03          | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 0.82/1.03      inference('demod', [status(thm)], ['24', '27'])).
% 0.82/1.03  thf('29', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.82/1.03      inference('demod', [status(thm)], ['0', '3'])).
% 0.82/1.03  thf('30', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.82/1.03      inference('sup-', [status(thm)], ['28', '29'])).
% 0.82/1.03  thf('31', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 0.82/1.03      inference('demod', [status(thm)], ['11', '30'])).
% 0.82/1.03  thf('32', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(redefinition_k1_relset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.03       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.82/1.03  thf('33', plain,
% 0.82/1.03      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.82/1.03         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.82/1.03          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.82/1.03  thf('34', plain,
% 0.82/1.03      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['32', '33'])).
% 0.82/1.03  thf('35', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.82/1.03      inference('demod', [status(thm)], ['8', '31', '34'])).
% 0.82/1.03  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.82/1.03  thf(zf_stmt_8, axiom,
% 0.82/1.03    (![C:$i,B:$i,A:$i]:
% 0.82/1.03     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 0.82/1.03       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.82/1.03  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.82/1.03  thf(zf_stmt_10, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.82/1.03       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.82/1.03           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 0.82/1.03         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 0.82/1.03  thf('36', plain,
% 0.82/1.03      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.82/1.03         (((k1_relat_1 @ X51) != (X50))
% 0.82/1.03          | ~ (zip_tseitin_2 @ (sk_D @ X51 @ X52 @ X50) @ X51 @ X52 @ X50)
% 0.82/1.03          | (zip_tseitin_3 @ X51 @ X52 @ X50)
% 0.82/1.03          | ~ (v1_funct_1 @ X51)
% 0.82/1.03          | ~ (v1_relat_1 @ X51))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.82/1.03  thf('37', plain,
% 0.82/1.03      (![X51 : $i, X52 : $i]:
% 0.82/1.03         (~ (v1_relat_1 @ X51)
% 0.82/1.03          | ~ (v1_funct_1 @ X51)
% 0.82/1.03          | (zip_tseitin_3 @ X51 @ X52 @ (k1_relat_1 @ X51))
% 0.82/1.03          | ~ (zip_tseitin_2 @ (sk_D @ X51 @ X52 @ (k1_relat_1 @ X51)) @ X51 @ 
% 0.82/1.03               X52 @ (k1_relat_1 @ X51)))),
% 0.82/1.03      inference('simplify', [status(thm)], ['36'])).
% 0.82/1.03  thf('38', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 0.82/1.03             (k1_relat_1 @ sk_D_1))
% 0.82/1.03          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.82/1.03          | ~ (v1_funct_1 @ sk_D_1)
% 0.82/1.03          | ~ (v1_relat_1 @ sk_D_1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['35', '37'])).
% 0.82/1.03  thf('39', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.82/1.03      inference('demod', [status(thm)], ['8', '31', '34'])).
% 0.82/1.03  thf('40', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.82/1.03      inference('demod', [status(thm)], ['8', '31', '34'])).
% 0.82/1.03  thf('41', plain, ((v1_funct_1 @ sk_D_1)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('42', plain, ((v1_relat_1 @ sk_D_1)),
% 0.82/1.03      inference('sup-', [status(thm)], ['25', '26'])).
% 0.82/1.03  thf('43', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.82/1.03          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.82/1.03  thf('44', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 0.82/1.03          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['5', '43'])).
% 0.82/1.03  thf(t1_subset, axiom,
% 0.82/1.03    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.82/1.03  thf('45', plain,
% 0.82/1.03      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.82/1.03      inference('cnf', [status(esa)], [t1_subset])).
% 0.82/1.03  thf('46', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.82/1.03          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.82/1.03  thf('47', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(redefinition_k3_funct_2, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.03     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.82/1.03         ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.82/1.03         ( m1_subset_1 @ D @ A ) ) =>
% 0.82/1.03       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.82/1.03  thf('48', plain,
% 0.82/1.03      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.82/1.03          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.82/1.03          | ~ (v1_funct_1 @ X38)
% 0.82/1.03          | (v1_xboole_0 @ X39)
% 0.82/1.03          | ~ (m1_subset_1 @ X41 @ X39)
% 0.82/1.03          | ((k3_funct_2 @ X39 @ X40 @ X38 @ X41) = (k1_funct_1 @ X38 @ X41)))),
% 0.82/1.03      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.82/1.03  thf('49', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.82/1.03            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.82/1.03          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.82/1.03          | (v1_xboole_0 @ sk_B)
% 0.82/1.03          | ~ (v1_funct_1 @ sk_D_1)
% 0.82/1.03          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 0.82/1.03      inference('sup-', [status(thm)], ['47', '48'])).
% 0.82/1.03  thf('50', plain, ((v1_funct_1 @ sk_D_1)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('51', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('52', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.82/1.03            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.82/1.03          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.82/1.03          | (v1_xboole_0 @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.82/1.03  thf('53', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('54', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.82/1.03          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.82/1.03              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 0.82/1.03      inference('clc', [status(thm)], ['52', '53'])).
% 0.82/1.03  thf('55', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.82/1.03          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 0.82/1.03              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 0.82/1.03      inference('sup-', [status(thm)], ['46', '54'])).
% 0.82/1.03  thf('56', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.82/1.03          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.82/1.03  thf('57', plain,
% 0.82/1.03      (![X53 : $i]:
% 0.82/1.03         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X53) @ sk_A)
% 0.82/1.03          | ~ (m1_subset_1 @ X53 @ sk_B))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('58', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.82/1.03          | (r2_hidden @ 
% 0.82/1.03             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.82/1.03             sk_A))),
% 0.82/1.03      inference('sup-', [status(thm)], ['56', '57'])).
% 0.82/1.03  thf('59', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.82/1.03           sk_A)
% 0.82/1.03          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.82/1.03          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.82/1.03      inference('sup+', [status(thm)], ['55', '58'])).
% 0.82/1.03  thf('60', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.82/1.03          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.82/1.03             sk_A))),
% 0.82/1.03      inference('simplify', [status(thm)], ['59'])).
% 0.82/1.03  thf('61', plain,
% 0.82/1.03      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.82/1.03         ((zip_tseitin_2 @ X43 @ X44 @ X45 @ X46)
% 0.82/1.03          | ~ (r2_hidden @ (k1_funct_1 @ X44 @ X43) @ X45))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.03  thf('62', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.82/1.03          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['60', '61'])).
% 0.82/1.03  thf('63', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.82/1.03          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.82/1.03      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.82/1.03  thf('64', plain,
% 0.82/1.03      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 0.82/1.03        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 0.82/1.03      inference('sup-', [status(thm)], ['62', '63'])).
% 0.82/1.03  thf('65', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 0.82/1.03      inference('simplify', [status(thm)], ['64'])).
% 0.82/1.03  thf('66', plain,
% 0.82/1.03      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.82/1.03         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.82/1.03          | ~ (zip_tseitin_3 @ X47 @ X48 @ X49))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.82/1.03  thf('67', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['65', '66'])).
% 0.82/1.03  thf('68', plain,
% 0.82/1.03      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.82/1.03         ((v5_relat_1 @ X12 @ X14)
% 0.82/1.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.82/1.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.82/1.03  thf('69', plain, ((v5_relat_1 @ sk_D_1 @ sk_A)),
% 0.82/1.03      inference('sup-', [status(thm)], ['67', '68'])).
% 0.82/1.03  thf('70', plain,
% 0.82/1.03      (![X7 : $i, X8 : $i]:
% 0.82/1.03         (~ (v5_relat_1 @ X7 @ X8)
% 0.82/1.03          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.82/1.03          | ~ (v1_relat_1 @ X7))),
% 0.82/1.03      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.82/1.03  thf('71', plain,
% 0.82/1.03      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A))),
% 0.82/1.03      inference('sup-', [status(thm)], ['69', '70'])).
% 0.82/1.03  thf('72', plain, ((v1_relat_1 @ sk_D_1)),
% 0.82/1.03      inference('sup-', [status(thm)], ['25', '26'])).
% 0.82/1.03  thf('73', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.82/1.03      inference('demod', [status(thm)], ['71', '72'])).
% 0.82/1.03  thf('74', plain, ($false), inference('demod', [status(thm)], ['4', '73'])).
% 0.82/1.03  
% 0.82/1.03  % SZS output end Refutation
% 0.82/1.03  
% 0.82/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
