%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1027+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hl6RHmGsMc

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 54.64s
% Output     : Refutation 54.64s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 159 expanded)
%              Number of leaves         :   35 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  604 (1751 expanded)
%              Number of equality atoms :   28 (  69 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_99_type,type,(
    sk_B_99: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(zip_tseitin_97_type,type,(
    zip_tseitin_97: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_98_type,type,(
    zip_tseitin_98: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_110_type,type,(
    sk_C_110: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X1729: $i] :
      ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ X1729 ) ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ! [X1729: $i] :
      ( m1_subset_1 @ ( o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X1729 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc2_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( ~ ( v1_subset_1 @ ( B @ A ) )
           => ~ ( v1_xboole_0 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X1806: $i,X1807: $i] :
      ( ~ ( m1_subset_1 @ ( X1806 @ ( k1_zfmisc_1 @ X1807 ) ) )
      | ~ ( v1_xboole_0 @ X1806 )
      | ( v1_subset_1 @ ( X1806 @ X1807 ) )
      | ( v1_xboole_0 @ X1807 ) ) ),
    inference(cnf,[status(esa)],[cc2_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ ( o_0_0_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ ( o_0_0_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X995: $i,X996: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( X995 @ X996 ) ) )
      | ~ ( v1_xboole_0 @ X996 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
     => ( ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
          & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
       => ( ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('8',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('9',plain,(
    ! [X1803: $i,X1804: $i] :
      ( ~ ( m1_subset_1 @ ( X1803 @ ( k1_zfmisc_1 @ X1804 ) ) )
      | ( v1_xboole_0 @ X1803 )
      | ~ ( v1_xboole_0 @ X1804 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) )
    | ( v1_xboole_0 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ sk_B_99 )
    | ( v1_xboole_0 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( v1_subset_1 @ ( o_0_0_xboole_0 @ sk_B_99 ) )
    | ( v1_xboole_0 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X3595: $i,X3596: $i,X3597: $i] :
      ( ( ( k1_relset_1 @ ( X3596 @ ( X3597 @ X3595 ) ) )
        = ( k1_relat_1 @ X3595 ) )
      | ~ ( m1_subset_1 @ ( X3595 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3596 @ X3597 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ ( sk_A_16 @ ( sk_B_99 @ sk_C_110 ) ) )
    = ( k1_relat_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_relset_1 @ ( sk_A_16 @ ( sk_B_99 @ sk_C_110 ) ) )
    = sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relat_1 @ sk_C_110 )
    = sk_A_16 ),
    inference('sup+',[status(thm)],['15','16'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X2150: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X2150 ) )
      | ~ ( v1_xboole_0 @ X2150 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_A_16 )
    | ~ ( v1_xboole_0 @ sk_C_110 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_subset_1 @ ( o_0_0_xboole_0 @ sk_B_99 ) )
    | ( v1_xboole_0 @ sk_A_16 ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
         => ( v1_partfun1 @ ( C @ A ) ) ) ) )).

thf('22',plain,(
    ! [X4635: $i,X4636: $i,X4637: $i] :
      ( ~ ( v1_xboole_0 @ X4635 )
      | ~ ( m1_subset_1 @ ( X4636 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X4635 @ X4637 ) ) ) ) )
      | ( v1_partfun1 @ ( X4636 @ X4635 ) ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('23',plain,
    ( ( v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) )
    | ~ ( v1_xboole_0 @ sk_A_16 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ ( C @ A ) ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ ( C @ ( A @ B ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X4632: $i,X4633: $i,X4634: $i] :
      ( ~ ( v1_funct_1 @ X4632 )
      | ~ ( v1_partfun1 @ ( X4632 @ X4633 ) )
      | ( v1_funct_2 @ ( X4632 @ ( X4633 @ X4634 ) ) )
      | ~ ( m1_subset_1 @ ( X4632 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X4633 @ X4634 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('26',plain,
    ( ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
    | ~ ( v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) )
    | ~ ( v1_funct_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
    | ~ ( v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_C_110 )
    | ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
    | ~ ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
   <= ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C_110 )
   <= ~ ( v1_funct_1 @ sk_C_110 ) ),
    inference(split,[status(esa)],['29'])).

thf('33',plain,(
    v1_funct_1 @ sk_C_110 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf('36',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
    | ~ ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) )
    | ~ ( v1_funct_1 @ sk_C_110 ) ),
    inference(split,[status(esa)],['29'])).

thf('38',plain,(
    ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['33','36','37'])).

thf('39',plain,(
    ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) ) ),
    inference(simpl_trail,[status(thm)],['30','38'])).

thf('40',plain,(
    ~ ( v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) ) ),
    inference(clc,[status(thm)],['28','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_A_16 ) ),
    inference(clc,[status(thm)],['23','40'])).

thf('42',plain,(
    v1_subset_1 @ ( o_0_0_xboole_0 @ sk_B_99 ) ),
    inference('sup-',[status(thm)],['20','41'])).

thf('43',plain,(
    ! [X1729: $i] :
      ( m1_subset_1 @ ( o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X1729 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ~ ( v1_subset_1 @ ( B @ A ) ) ) ) )).

thf('44',plain,(
    ! [X1811: $i,X1812: $i] :
      ( ~ ( m1_subset_1 @ ( X1811 @ ( k1_zfmisc_1 @ X1812 ) ) )
      | ~ ( v1_subset_1 @ ( X1811 @ X1812 ) )
      | ~ ( v1_xboole_0 @ X1812 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_subset_1 @ ( o_0_0_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ sk_B_99 ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
          <=> ( A
              = ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_97 @ ( B @ A ) ) ) )).

thf('47',plain,(
    ! [X4653: $i,X4654: $i] :
      ( ( zip_tseitin_97 @ ( X4653 @ X4654 ) )
      | ( X4653 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('49',plain,(
    ! [X4653: $i,X4654: $i] :
      ( ( zip_tseitin_97 @ ( X4653 @ X4654 ) )
      | ( X4653 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_98: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_98 @ ( C @ ( B @ A ) ) )
     => ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
      <=> ( A
          = ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_97: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( zip_tseitin_97 @ ( B @ A ) )
         => ( zip_tseitin_98 @ ( C @ ( B @ A ) ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X4658: $i,X4659: $i,X4660: $i] :
      ( ~ ( zip_tseitin_97 @ ( X4658 @ X4659 ) )
      | ( zip_tseitin_98 @ ( X4660 @ ( X4658 @ X4659 ) ) )
      | ~ ( m1_subset_1 @ ( X4660 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X4659 @ X4658 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_99 @ sk_A_16 ) ) )
    | ~ ( zip_tseitin_97 @ ( sk_B_99 @ sk_A_16 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relset_1 @ ( sk_A_16 @ ( sk_B_99 @ sk_C_110 ) ) )
    = sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X4655: $i,X4656: $i,X4657: $i] :
      ( ( X4655
       != ( k1_relset_1 @ ( X4655 @ ( X4656 @ X4657 ) ) ) )
      | ( v1_funct_2 @ ( X4657 @ ( X4655 @ X4656 ) ) )
      | ~ ( zip_tseitin_98 @ ( X4657 @ ( X4656 @ X4655 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,
    ( ( sk_A_16 != sk_A_16 )
    | ~ ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_99 @ sk_A_16 ) ) )
    | ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
    | ~ ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_99 @ sk_A_16 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) ) ),
    inference(simpl_trail,[status(thm)],['30','38'])).

thf('58',plain,(
    ~ ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_99 @ sk_A_16 ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( zip_tseitin_97 @ ( sk_B_99 @ sk_A_16 ) ) ),
    inference(clc,[status(thm)],['52','58'])).

thf('60',plain,(
    sk_B_99 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['46','60','61'])).

%------------------------------------------------------------------------------
