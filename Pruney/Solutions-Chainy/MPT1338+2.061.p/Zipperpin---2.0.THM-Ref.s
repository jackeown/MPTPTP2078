%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1C2aDxyPje

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:57 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  288 (3969 expanded)
%              Number of leaves         :   47 (1158 expanded)
%              Depth                    :   32
%              Number of atoms          : 2565 (100541 expanded)
%              Number of equality atoms :  162 (5083 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('2',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( v1_partfun1 @ X14 @ X15 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X31: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('50',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf('63',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('70',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('71',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','72'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('74',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X32 @ X34 )
       != X32 )
      | ~ ( v2_funct_1 @ X34 )
      | ( ( k2_tops_2 @ X33 @ X32 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('92',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['91','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','89','90','104'])).

thf('106',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('108',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','47','48','49','106','107'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','72'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('111',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('120',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['105'])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('123',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('124',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('125',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('126',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','131'])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('134',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('136',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46'])).

thf('137',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('138',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','138'])).

thf('140',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','139'])).

thf('141',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('148',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['146','147'])).

thf('149',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['108','148'])).

thf('150',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('152',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X27 ) @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('155',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('158',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('161',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('162',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('164',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156','159','164','165'])).

thf('167',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['150','166'])).

thf('168',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('169',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['170'])).

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

thf('172',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('173',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('175',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('176',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('177',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('180',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('181',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['177','178','179','180','181'])).

thf('183',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['174','182'])).

thf('184',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('185',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

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

thf('188',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('189',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('191',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('192',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('195',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('196',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( v1_partfun1 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('197',plain,
    ( ~ ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ~ ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['194','197'])).

thf('199',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('200',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('201',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('202',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('203',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('205',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != X25 )
      | ( v1_partfun1 @ X26 @ X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('206',plain,(
    ! [X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v4_relat_1 @ X26 @ ( k1_relat_1 @ X26 ) )
      | ( v1_partfun1 @ X26 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','206'])).

thf('208',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['203','207'])).

thf('209',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('211',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('213',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('217',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['208','213','214','215','216'])).

thf('218',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['200','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf('223',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['198','199','222','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['193','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['190','225'])).

thf('227',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('228',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('230',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('231',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['189','231'])).

thf('233',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['173','232'])).

thf('234',plain,(
    ( u1_struct_0 @ sk_B )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['149','233'])).

thf('235',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','234'])).

thf('236',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('237',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,(
    $false ),
    inference(simplify,[status(thm)],['238'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1C2aDxyPje
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.33/1.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.33/1.51  % Solved by: fo/fo7.sh
% 1.33/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.33/1.51  % done 670 iterations in 1.055s
% 1.33/1.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.33/1.51  % SZS output start Refutation
% 1.33/1.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.33/1.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.33/1.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.33/1.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.33/1.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.33/1.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.33/1.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.33/1.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.33/1.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.33/1.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.33/1.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.33/1.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.33/1.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.33/1.51  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.33/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.33/1.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.33/1.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.33/1.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.33/1.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.33/1.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.33/1.51  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.33/1.51  thf(sk_B_type, type, sk_B: $i).
% 1.33/1.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.33/1.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.33/1.51  thf(sk_C_type, type, sk_C: $i).
% 1.33/1.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.33/1.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.33/1.51  thf(d3_struct_0, axiom,
% 1.33/1.51    (![A:$i]:
% 1.33/1.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.33/1.51  thf('0', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('1', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf(t62_tops_2, conjecture,
% 1.33/1.51    (![A:$i]:
% 1.33/1.51     ( ( l1_struct_0 @ A ) =>
% 1.33/1.51       ( ![B:$i]:
% 1.33/1.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.33/1.51           ( ![C:$i]:
% 1.33/1.51             ( ( ( v1_funct_1 @ C ) & 
% 1.33/1.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.33/1.51                 ( m1_subset_1 @
% 1.33/1.51                   C @ 
% 1.33/1.51                   ( k1_zfmisc_1 @
% 1.33/1.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.33/1.51               ( ( ( ( k2_relset_1 @
% 1.33/1.51                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.33/1.51                     ( k2_struct_0 @ B ) ) & 
% 1.33/1.51                   ( v2_funct_1 @ C ) ) =>
% 1.33/1.51                 ( ( ( k1_relset_1 @
% 1.33/1.51                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.33/1.51                       ( k2_tops_2 @
% 1.33/1.51                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.33/1.51                     ( k2_struct_0 @ B ) ) & 
% 1.33/1.51                   ( ( k2_relset_1 @
% 1.33/1.51                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.33/1.51                       ( k2_tops_2 @
% 1.33/1.51                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.33/1.51                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.33/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.33/1.51    (~( ![A:$i]:
% 1.33/1.51        ( ( l1_struct_0 @ A ) =>
% 1.33/1.51          ( ![B:$i]:
% 1.33/1.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.33/1.51              ( ![C:$i]:
% 1.33/1.51                ( ( ( v1_funct_1 @ C ) & 
% 1.33/1.51                    ( v1_funct_2 @
% 1.33/1.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.33/1.51                    ( m1_subset_1 @
% 1.33/1.51                      C @ 
% 1.33/1.51                      ( k1_zfmisc_1 @
% 1.33/1.51                        ( k2_zfmisc_1 @
% 1.33/1.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.33/1.51                  ( ( ( ( k2_relset_1 @
% 1.33/1.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.33/1.51                        ( k2_struct_0 @ B ) ) & 
% 1.33/1.51                      ( v2_funct_1 @ C ) ) =>
% 1.33/1.51                    ( ( ( k1_relset_1 @
% 1.33/1.51                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.33/1.51                          ( k2_tops_2 @
% 1.33/1.51                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.33/1.51                        ( k2_struct_0 @ B ) ) & 
% 1.33/1.51                      ( ( k2_relset_1 @
% 1.33/1.51                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.33/1.51                          ( k2_tops_2 @
% 1.33/1.51                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.33/1.51                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.33/1.51    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.33/1.51  thf('2', plain,
% 1.33/1.51      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          != (k2_struct_0 @ sk_B))
% 1.33/1.51        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51            != (k2_struct_0 @ sk_A)))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('3', plain,
% 1.33/1.51      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          != (k2_struct_0 @ sk_B)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_B))))),
% 1.33/1.51      inference('split', [status(esa)], ['2'])).
% 1.33/1.51  thf('4', plain,
% 1.33/1.51      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51           != (k2_struct_0 @ sk_B))
% 1.33/1.51         | ~ (l1_struct_0 @ sk_B)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_B))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['1', '3'])).
% 1.33/1.51  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('6', plain,
% 1.33/1.51      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          != (k2_struct_0 @ sk_B)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['4', '5'])).
% 1.33/1.51  thf('7', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('8', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('9', plain,
% 1.33/1.51      (((m1_subset_1 @ sk_C @ 
% 1.33/1.51         (k1_zfmisc_1 @ 
% 1.33/1.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['7', '8'])).
% 1.33/1.51  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('11', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['9', '10'])).
% 1.33/1.51  thf('12', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf(redefinition_k2_relset_1, axiom,
% 1.33/1.51    (![A:$i,B:$i,C:$i]:
% 1.33/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.33/1.51  thf('13', plain,
% 1.33/1.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.33/1.51         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.33/1.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.33/1.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.33/1.51  thf('14', plain,
% 1.33/1.51      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51         = (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('sup-', [status(thm)], ['12', '13'])).
% 1.33/1.51  thf('15', plain,
% 1.33/1.51      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51         = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('17', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.33/1.51      inference('demod', [status(thm)], ['11', '16'])).
% 1.33/1.51  thf(cc5_funct_2, axiom,
% 1.33/1.51    (![A:$i,B:$i]:
% 1.33/1.51     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.33/1.51       ( ![C:$i]:
% 1.33/1.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.51           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.33/1.51             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.33/1.51  thf('18', plain,
% 1.33/1.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.33/1.51         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.33/1.51          | (v1_partfun1 @ X14 @ X15)
% 1.33/1.51          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 1.33/1.51          | ~ (v1_funct_1 @ X14)
% 1.33/1.51          | (v1_xboole_0 @ X16))),
% 1.33/1.51      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.33/1.51  thf('19', plain,
% 1.33/1.51      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.33/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.33/1.51        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.33/1.51        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['17', '18'])).
% 1.33/1.51  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('21', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('22', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('23', plain,
% 1.33/1.51      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['21', '22'])).
% 1.33/1.51  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('25', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['23', '24'])).
% 1.33/1.51  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('27', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['25', '26'])).
% 1.33/1.51  thf('28', plain,
% 1.33/1.51      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.33/1.51        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.33/1.51      inference('demod', [status(thm)], ['19', '20', '27'])).
% 1.33/1.51  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf(fc5_struct_0, axiom,
% 1.33/1.51    (![A:$i]:
% 1.33/1.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.33/1.51       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.33/1.51  thf('30', plain,
% 1.33/1.51      (![X31 : $i]:
% 1.33/1.51         (~ (v1_xboole_0 @ (k2_struct_0 @ X31))
% 1.33/1.51          | ~ (l1_struct_0 @ X31)
% 1.33/1.51          | (v2_struct_0 @ X31))),
% 1.33/1.51      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.33/1.51  thf('31', plain,
% 1.33/1.51      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.33/1.51        | (v2_struct_0 @ sk_B)
% 1.33/1.51        | ~ (l1_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup-', [status(thm)], ['29', '30'])).
% 1.33/1.51  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('33', plain,
% 1.33/1.51      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['31', '32'])).
% 1.33/1.51  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('35', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('clc', [status(thm)], ['33', '34'])).
% 1.33/1.51  thf('36', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.33/1.51      inference('clc', [status(thm)], ['28', '35'])).
% 1.33/1.51  thf(d4_partfun1, axiom,
% 1.33/1.51    (![A:$i,B:$i]:
% 1.33/1.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.33/1.51       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.33/1.51  thf('37', plain,
% 1.33/1.51      (![X25 : $i, X26 : $i]:
% 1.33/1.51         (~ (v1_partfun1 @ X26 @ X25)
% 1.33/1.51          | ((k1_relat_1 @ X26) = (X25))
% 1.33/1.51          | ~ (v4_relat_1 @ X26 @ X25)
% 1.33/1.51          | ~ (v1_relat_1 @ X26))),
% 1.33/1.51      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.33/1.51  thf('38', plain,
% 1.33/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.33/1.51        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.33/1.51        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['36', '37'])).
% 1.33/1.51  thf('39', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf(cc2_relat_1, axiom,
% 1.33/1.51    (![A:$i]:
% 1.33/1.51     ( ( v1_relat_1 @ A ) =>
% 1.33/1.51       ( ![B:$i]:
% 1.33/1.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.33/1.51  thf('40', plain,
% 1.33/1.51      (![X0 : $i, X1 : $i]:
% 1.33/1.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.33/1.51          | (v1_relat_1 @ X0)
% 1.33/1.51          | ~ (v1_relat_1 @ X1))),
% 1.33/1.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.33/1.51  thf('41', plain,
% 1.33/1.51      ((~ (v1_relat_1 @ 
% 1.33/1.51           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.33/1.51        | (v1_relat_1 @ sk_C))),
% 1.33/1.51      inference('sup-', [status(thm)], ['39', '40'])).
% 1.33/1.51  thf(fc6_relat_1, axiom,
% 1.33/1.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.33/1.51  thf('42', plain,
% 1.33/1.51      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.33/1.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.33/1.51  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 1.33/1.51      inference('demod', [status(thm)], ['41', '42'])).
% 1.33/1.51  thf('44', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf(cc2_relset_1, axiom,
% 1.33/1.51    (![A:$i,B:$i,C:$i]:
% 1.33/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.33/1.51  thf('45', plain,
% 1.33/1.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.33/1.51         ((v4_relat_1 @ X5 @ X6)
% 1.33/1.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.33/1.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.33/1.51  thf('46', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.33/1.51      inference('sup-', [status(thm)], ['44', '45'])).
% 1.33/1.51  thf('47', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['38', '43', '46'])).
% 1.33/1.51  thf('48', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['38', '43', '46'])).
% 1.33/1.51  thf('49', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('50', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('51', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('52', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('53', plain,
% 1.33/1.51      (((m1_subset_1 @ sk_C @ 
% 1.33/1.51         (k1_zfmisc_1 @ 
% 1.33/1.51          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_A))),
% 1.33/1.51      inference('sup+', [status(thm)], ['51', '52'])).
% 1.33/1.51  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('55', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['53', '54'])).
% 1.33/1.51  thf('56', plain,
% 1.33/1.51      (((m1_subset_1 @ sk_C @ 
% 1.33/1.51         (k1_zfmisc_1 @ 
% 1.33/1.51          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['50', '55'])).
% 1.33/1.51  thf('57', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('58', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['56', '57'])).
% 1.33/1.51  thf('59', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('60', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.33/1.51      inference('demod', [status(thm)], ['58', '59'])).
% 1.33/1.51  thf('61', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('62', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.33/1.51      inference('clc', [status(thm)], ['28', '35'])).
% 1.33/1.51  thf('63', plain,
% 1.33/1.51      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.33/1.51      inference('sup+', [status(thm)], ['61', '62'])).
% 1.33/1.51  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('65', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['63', '64'])).
% 1.33/1.51  thf('66', plain,
% 1.33/1.51      (![X25 : $i, X26 : $i]:
% 1.33/1.51         (~ (v1_partfun1 @ X26 @ X25)
% 1.33/1.51          | ((k1_relat_1 @ X26) = (X25))
% 1.33/1.51          | ~ (v4_relat_1 @ X26 @ X25)
% 1.33/1.51          | ~ (v1_relat_1 @ X26))),
% 1.33/1.51      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.33/1.51  thf('67', plain,
% 1.33/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.33/1.51        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.33/1.51        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['65', '66'])).
% 1.33/1.51  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 1.33/1.51      inference('demod', [status(thm)], ['41', '42'])).
% 1.33/1.51  thf('69', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['53', '54'])).
% 1.33/1.51  thf('70', plain,
% 1.33/1.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.33/1.51         ((v4_relat_1 @ X5 @ X6)
% 1.33/1.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.33/1.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.33/1.51  thf('71', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.33/1.51      inference('sup-', [status(thm)], ['69', '70'])).
% 1.33/1.51  thf('72', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['67', '68', '71'])).
% 1.33/1.51  thf('73', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.33/1.51      inference('demod', [status(thm)], ['60', '72'])).
% 1.33/1.51  thf(d4_tops_2, axiom,
% 1.33/1.51    (![A:$i,B:$i,C:$i]:
% 1.33/1.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.33/1.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.33/1.51       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.33/1.51         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.33/1.51  thf('74', plain,
% 1.33/1.51      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.33/1.51         (((k2_relset_1 @ X33 @ X32 @ X34) != (X32))
% 1.33/1.51          | ~ (v2_funct_1 @ X34)
% 1.33/1.51          | ((k2_tops_2 @ X33 @ X32 @ X34) = (k2_funct_1 @ X34))
% 1.33/1.51          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.33/1.51          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 1.33/1.51          | ~ (v1_funct_1 @ X34))),
% 1.33/1.51      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.33/1.51  thf('75', plain,
% 1.33/1.51      ((~ (v1_funct_1 @ sk_C)
% 1.33/1.51        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.33/1.51        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.33/1.51            = (k2_funct_1 @ sk_C))
% 1.33/1.51        | ~ (v2_funct_1 @ sk_C)
% 1.33/1.51        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.33/1.51            != (k2_relat_1 @ sk_C)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['73', '74'])).
% 1.33/1.51  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('77', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('78', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('79', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('80', plain,
% 1.33/1.51      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_A))),
% 1.33/1.51      inference('sup+', [status(thm)], ['78', '79'])).
% 1.33/1.51  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('82', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['80', '81'])).
% 1.33/1.51  thf('83', plain,
% 1.33/1.51      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['77', '82'])).
% 1.33/1.51  thf('84', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('85', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['83', '84'])).
% 1.33/1.51  thf('86', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('87', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['85', '86'])).
% 1.33/1.51  thf('88', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['67', '68', '71'])).
% 1.33/1.51  thf('89', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['87', '88'])).
% 1.33/1.51  thf('90', plain, ((v2_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('91', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('92', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('93', plain,
% 1.33/1.51      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51         = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('94', plain,
% 1.33/1.51      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51          = (k2_struct_0 @ sk_B))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_A))),
% 1.33/1.51      inference('sup+', [status(thm)], ['92', '93'])).
% 1.33/1.51  thf('95', plain, ((l1_struct_0 @ sk_A)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('96', plain,
% 1.33/1.51      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51         = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['94', '95'])).
% 1.33/1.51  thf('97', plain,
% 1.33/1.51      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51          = (k2_struct_0 @ sk_B))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['91', '96'])).
% 1.33/1.51  thf('98', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('99', plain,
% 1.33/1.51      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51         = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['97', '98'])).
% 1.33/1.51  thf('100', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('101', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('102', plain,
% 1.33/1.51      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.33/1.51         = (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['99', '100', '101'])).
% 1.33/1.51  thf('103', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['67', '68', '71'])).
% 1.33/1.51  thf('104', plain,
% 1.33/1.51      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.33/1.51         = (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['102', '103'])).
% 1.33/1.51  thf('105', plain,
% 1.33/1.51      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.33/1.51          = (k2_funct_1 @ sk_C))
% 1.33/1.51        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.33/1.51      inference('demod', [status(thm)], ['75', '76', '89', '90', '104'])).
% 1.33/1.51  thf('106', plain,
% 1.33/1.51      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.33/1.51         = (k2_funct_1 @ sk_C))),
% 1.33/1.51      inference('simplify', [status(thm)], ['105'])).
% 1.33/1.51  thf('107', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('108', plain,
% 1.33/1.51      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.33/1.51          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['6', '47', '48', '49', '106', '107'])).
% 1.33/1.51  thf(t55_funct_1, axiom,
% 1.33/1.51    (![A:$i]:
% 1.33/1.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.33/1.51       ( ( v2_funct_1 @ A ) =>
% 1.33/1.51         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.33/1.51           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.33/1.51  thf('109', plain,
% 1.33/1.51      (![X4 : $i]:
% 1.33/1.51         (~ (v2_funct_1 @ X4)
% 1.33/1.51          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 1.33/1.51          | ~ (v1_funct_1 @ X4)
% 1.33/1.51          | ~ (v1_relat_1 @ X4))),
% 1.33/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.33/1.51  thf('110', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.33/1.51      inference('demod', [status(thm)], ['60', '72'])).
% 1.33/1.51  thf(t31_funct_2, axiom,
% 1.33/1.51    (![A:$i,B:$i,C:$i]:
% 1.33/1.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.33/1.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.33/1.51       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.33/1.51         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.33/1.51           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.33/1.51           ( m1_subset_1 @
% 1.33/1.51             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.33/1.51  thf('111', plain,
% 1.33/1.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.33/1.51         (~ (v2_funct_1 @ X27)
% 1.33/1.51          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 1.33/1.51          | (m1_subset_1 @ (k2_funct_1 @ X27) @ 
% 1.33/1.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.33/1.51          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 1.33/1.51          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 1.33/1.51          | ~ (v1_funct_1 @ X27))),
% 1.33/1.51      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.33/1.51  thf('112', plain,
% 1.33/1.51      ((~ (v1_funct_1 @ sk_C)
% 1.33/1.51        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.33/1.51        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51           (k1_zfmisc_1 @ 
% 1.33/1.51            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.33/1.51        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.33/1.51            != (k2_relat_1 @ sk_C))
% 1.33/1.51        | ~ (v2_funct_1 @ sk_C))),
% 1.33/1.51      inference('sup-', [status(thm)], ['110', '111'])).
% 1.33/1.51  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('114', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['87', '88'])).
% 1.33/1.51  thf('115', plain,
% 1.33/1.51      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.33/1.51         = (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['102', '103'])).
% 1.33/1.51  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('117', plain,
% 1.33/1.51      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51         (k1_zfmisc_1 @ 
% 1.33/1.51          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.33/1.51        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.33/1.51      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 1.33/1.51  thf('118', plain,
% 1.33/1.51      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.33/1.51      inference('simplify', [status(thm)], ['117'])).
% 1.33/1.51  thf('119', plain,
% 1.33/1.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.33/1.51         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.33/1.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.33/1.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.33/1.51  thf('120', plain,
% 1.33/1.51      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.33/1.51         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['118', '119'])).
% 1.33/1.51  thf('121', plain,
% 1.33/1.51      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.33/1.51         = (k2_funct_1 @ sk_C))),
% 1.33/1.51      inference('simplify', [status(thm)], ['105'])).
% 1.33/1.51  thf('122', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('123', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('124', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('125', plain,
% 1.33/1.51      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          != (k2_struct_0 @ sk_A)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('split', [status(esa)], ['2'])).
% 1.33/1.51  thf('126', plain,
% 1.33/1.51      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51           != (k2_struct_0 @ sk_A))
% 1.33/1.51         | ~ (l1_struct_0 @ sk_B)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['124', '125'])).
% 1.33/1.51  thf('127', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('128', plain,
% 1.33/1.51      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          != (k2_struct_0 @ sk_A)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('demod', [status(thm)], ['126', '127'])).
% 1.33/1.51  thf('129', plain,
% 1.33/1.51      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51           != (k2_struct_0 @ sk_A))
% 1.33/1.51         | ~ (l1_struct_0 @ sk_B)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['123', '128'])).
% 1.33/1.51  thf('130', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('131', plain,
% 1.33/1.51      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          != (k2_struct_0 @ sk_A)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('demod', [status(thm)], ['129', '130'])).
% 1.33/1.51  thf('132', plain,
% 1.33/1.51      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          != (k2_struct_0 @ sk_A)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['122', '131'])).
% 1.33/1.51  thf('133', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('134', plain,
% 1.33/1.51      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.33/1.51          != (k2_struct_0 @ sk_A)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('demod', [status(thm)], ['132', '133'])).
% 1.33/1.51  thf('135', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['38', '43', '46'])).
% 1.33/1.51  thf('136', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['38', '43', '46'])).
% 1.33/1.51  thf('137', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['67', '68', '71'])).
% 1.33/1.51  thf('138', plain,
% 1.33/1.51      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.33/1.51          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.33/1.51          != (k1_relat_1 @ sk_C)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 1.33/1.51  thf('139', plain,
% 1.33/1.51      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.33/1.51          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['121', '138'])).
% 1.33/1.51  thf('140', plain,
% 1.33/1.51      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['120', '139'])).
% 1.33/1.51  thf('141', plain,
% 1.33/1.51      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.33/1.51         | ~ (v1_relat_1 @ sk_C)
% 1.33/1.51         | ~ (v1_funct_1 @ sk_C)
% 1.33/1.51         | ~ (v2_funct_1 @ sk_C)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['109', '140'])).
% 1.33/1.51  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 1.33/1.51      inference('demod', [status(thm)], ['41', '42'])).
% 1.33/1.51  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('145', plain,
% 1.33/1.51      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.33/1.51         <= (~
% 1.33/1.51             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51                = (k2_struct_0 @ sk_A))))),
% 1.33/1.51      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 1.33/1.51  thf('146', plain,
% 1.33/1.51      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          = (k2_struct_0 @ sk_A)))),
% 1.33/1.51      inference('simplify', [status(thm)], ['145'])).
% 1.33/1.51  thf('147', plain,
% 1.33/1.51      (~
% 1.33/1.51       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          = (k2_struct_0 @ sk_B))) | 
% 1.33/1.51       ~
% 1.33/1.51       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          = (k2_struct_0 @ sk_A)))),
% 1.33/1.51      inference('split', [status(esa)], ['2'])).
% 1.33/1.51  thf('148', plain,
% 1.33/1.51      (~
% 1.33/1.51       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.33/1.51          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.33/1.51          = (k2_struct_0 @ sk_B)))),
% 1.33/1.51      inference('sat_resolution*', [status(thm)], ['146', '147'])).
% 1.33/1.51  thf('149', plain,
% 1.33/1.51      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.33/1.51         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('simpl_trail', [status(thm)], ['108', '148'])).
% 1.33/1.51  thf('150', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('151', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['53', '54'])).
% 1.33/1.51  thf('152', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['67', '68', '71'])).
% 1.33/1.51  thf('153', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['151', '152'])).
% 1.33/1.51  thf('154', plain,
% 1.33/1.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.33/1.51         (~ (v2_funct_1 @ X27)
% 1.33/1.51          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 1.33/1.51          | (v1_funct_2 @ (k2_funct_1 @ X27) @ X28 @ X29)
% 1.33/1.51          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 1.33/1.51          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 1.33/1.51          | ~ (v1_funct_1 @ X27))),
% 1.33/1.51      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.33/1.51  thf('155', plain,
% 1.33/1.51      ((~ (v1_funct_1 @ sk_C)
% 1.33/1.51        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.33/1.51        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.33/1.51           (k1_relat_1 @ sk_C))
% 1.33/1.51        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51            != (u1_struct_0 @ sk_B))
% 1.33/1.51        | ~ (v2_funct_1 @ sk_C))),
% 1.33/1.51      inference('sup-', [status(thm)], ['153', '154'])).
% 1.33/1.51  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('157', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['80', '81'])).
% 1.33/1.51  thf('158', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['67', '68', '71'])).
% 1.33/1.51  thf('159', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['157', '158'])).
% 1.33/1.51  thf('160', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['53', '54'])).
% 1.33/1.51  thf('161', plain,
% 1.33/1.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.33/1.51         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 1.33/1.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.33/1.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.33/1.51  thf('162', plain,
% 1.33/1.51      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51         = (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('sup-', [status(thm)], ['160', '161'])).
% 1.33/1.51  thf('163', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.33/1.51      inference('demod', [status(thm)], ['67', '68', '71'])).
% 1.33/1.51  thf('164', plain,
% 1.33/1.51      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51         = (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['162', '163'])).
% 1.33/1.51  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('166', plain,
% 1.33/1.51      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.33/1.51         (k1_relat_1 @ sk_C))
% 1.33/1.51        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.33/1.51      inference('demod', [status(thm)], ['155', '156', '159', '164', '165'])).
% 1.33/1.51  thf('167', plain,
% 1.33/1.51      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_B)
% 1.33/1.51        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.33/1.51           (k1_relat_1 @ sk_C)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['150', '166'])).
% 1.33/1.51  thf('168', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('170', plain,
% 1.33/1.51      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.33/1.51        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.33/1.51           (k1_relat_1 @ sk_C)))),
% 1.33/1.51      inference('demod', [status(thm)], ['167', '168', '169'])).
% 1.33/1.51  thf('171', plain,
% 1.33/1.51      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.33/1.51        (k1_relat_1 @ sk_C))),
% 1.33/1.51      inference('simplify', [status(thm)], ['170'])).
% 1.33/1.51  thf(d1_funct_2, axiom,
% 1.33/1.51    (![A:$i,B:$i,C:$i]:
% 1.33/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.33/1.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.33/1.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.33/1.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.33/1.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.33/1.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.33/1.51  thf(zf_stmt_1, axiom,
% 1.33/1.51    (![C:$i,B:$i,A:$i]:
% 1.33/1.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.33/1.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.33/1.51  thf('172', plain,
% 1.33/1.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.33/1.51         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.33/1.51          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.33/1.51          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.33/1.51  thf('173', plain,
% 1.33/1.51      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.33/1.51           (u1_struct_0 @ sk_B))
% 1.33/1.51        | ((u1_struct_0 @ sk_B)
% 1.33/1.51            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.33/1.51               (k2_funct_1 @ sk_C))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['171', '172'])).
% 1.33/1.51  thf('174', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('175', plain,
% 1.33/1.51      ((m1_subset_1 @ sk_C @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.33/1.51      inference('demod', [status(thm)], ['151', '152'])).
% 1.33/1.51  thf('176', plain,
% 1.33/1.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.33/1.51         (~ (v2_funct_1 @ X27)
% 1.33/1.51          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 1.33/1.51          | (m1_subset_1 @ (k2_funct_1 @ X27) @ 
% 1.33/1.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.33/1.51          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 1.33/1.51          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 1.33/1.51          | ~ (v1_funct_1 @ X27))),
% 1.33/1.51      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.33/1.51  thf('177', plain,
% 1.33/1.51      ((~ (v1_funct_1 @ sk_C)
% 1.33/1.51        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.33/1.51        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51           (k1_zfmisc_1 @ 
% 1.33/1.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 1.33/1.51        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51            != (u1_struct_0 @ sk_B))
% 1.33/1.51        | ~ (v2_funct_1 @ sk_C))),
% 1.33/1.51      inference('sup-', [status(thm)], ['175', '176'])).
% 1.33/1.51  thf('178', plain, ((v1_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('179', plain,
% 1.33/1.51      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['157', '158'])).
% 1.33/1.51  thf('180', plain,
% 1.33/1.51      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.33/1.51         = (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['162', '163'])).
% 1.33/1.51  thf('181', plain, ((v2_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('182', plain,
% 1.33/1.51      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51         (k1_zfmisc_1 @ 
% 1.33/1.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 1.33/1.51        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.33/1.51      inference('demod', [status(thm)], ['177', '178', '179', '180', '181'])).
% 1.33/1.51  thf('183', plain,
% 1.33/1.51      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_B)
% 1.33/1.51        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51           (k1_zfmisc_1 @ 
% 1.33/1.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.33/1.51      inference('sup-', [status(thm)], ['174', '182'])).
% 1.33/1.51  thf('184', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('185', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('186', plain,
% 1.33/1.51      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.33/1.51        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51           (k1_zfmisc_1 @ 
% 1.33/1.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 1.33/1.51      inference('demod', [status(thm)], ['183', '184', '185'])).
% 1.33/1.51  thf('187', plain,
% 1.33/1.51      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.33/1.51      inference('simplify', [status(thm)], ['186'])).
% 1.33/1.51  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.33/1.51  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.33/1.51  thf(zf_stmt_4, axiom,
% 1.33/1.51    (![B:$i,A:$i]:
% 1.33/1.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.33/1.51       ( zip_tseitin_0 @ B @ A ) ))).
% 1.33/1.51  thf(zf_stmt_5, axiom,
% 1.33/1.51    (![A:$i,B:$i,C:$i]:
% 1.33/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.33/1.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.33/1.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.33/1.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.33/1.51  thf('188', plain,
% 1.33/1.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.33/1.51         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.33/1.51          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.33/1.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.33/1.51  thf('189', plain,
% 1.33/1.51      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.33/1.51         (u1_struct_0 @ sk_B))
% 1.33/1.51        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['187', '188'])).
% 1.33/1.51  thf('190', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('191', plain,
% 1.33/1.51      (![X17 : $i, X18 : $i]:
% 1.33/1.51         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.33/1.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.33/1.51  thf('192', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.33/1.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.33/1.51  thf('193', plain,
% 1.33/1.51      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.33/1.51      inference('sup+', [status(thm)], ['191', '192'])).
% 1.33/1.51  thf('194', plain,
% 1.33/1.51      (![X30 : $i]:
% 1.33/1.51         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.33/1.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.33/1.51  thf('195', plain,
% 1.33/1.51      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 1.33/1.51      inference('simplify', [status(thm)], ['186'])).
% 1.33/1.51  thf(cc2_partfun1, axiom,
% 1.33/1.51    (![A:$i,B:$i]:
% 1.33/1.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 1.33/1.51       ( ![C:$i]:
% 1.33/1.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.33/1.51           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 1.33/1.51  thf('196', plain,
% 1.33/1.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.33/1.51         ((v1_xboole_0 @ X11)
% 1.33/1.51          | ~ (v1_xboole_0 @ X12)
% 1.33/1.51          | ~ (v1_partfun1 @ X13 @ X11)
% 1.33/1.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.33/1.51      inference('cnf', [status(esa)], [cc2_partfun1])).
% 1.33/1.51  thf('197', plain,
% 1.33/1.51      ((~ (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.33/1.51        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 1.33/1.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['195', '196'])).
% 1.33/1.51  thf('198', plain,
% 1.33/1.51      ((~ (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 1.33/1.51        | ~ (l1_struct_0 @ sk_B)
% 1.33/1.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.33/1.51        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['194', '197'])).
% 1.33/1.51  thf('199', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('200', plain,
% 1.33/1.51      (![X4 : $i]:
% 1.33/1.51         (~ (v2_funct_1 @ X4)
% 1.33/1.51          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 1.33/1.51          | ~ (v1_funct_1 @ X4)
% 1.33/1.51          | ~ (v1_relat_1 @ X4))),
% 1.33/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.33/1.51  thf('201', plain,
% 1.33/1.51      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.33/1.51      inference('simplify', [status(thm)], ['117'])).
% 1.33/1.51  thf('202', plain,
% 1.33/1.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.33/1.51         ((v4_relat_1 @ X5 @ X6)
% 1.33/1.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.33/1.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.33/1.51  thf('203', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('sup-', [status(thm)], ['201', '202'])).
% 1.33/1.51  thf('204', plain,
% 1.33/1.51      (![X4 : $i]:
% 1.33/1.51         (~ (v2_funct_1 @ X4)
% 1.33/1.51          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 1.33/1.51          | ~ (v1_funct_1 @ X4)
% 1.33/1.51          | ~ (v1_relat_1 @ X4))),
% 1.33/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.33/1.51  thf('205', plain,
% 1.33/1.51      (![X25 : $i, X26 : $i]:
% 1.33/1.51         (((k1_relat_1 @ X26) != (X25))
% 1.33/1.51          | (v1_partfun1 @ X26 @ X25)
% 1.33/1.51          | ~ (v4_relat_1 @ X26 @ X25)
% 1.33/1.51          | ~ (v1_relat_1 @ X26))),
% 1.33/1.51      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.33/1.51  thf('206', plain,
% 1.33/1.51      (![X26 : $i]:
% 1.33/1.51         (~ (v1_relat_1 @ X26)
% 1.33/1.51          | ~ (v4_relat_1 @ X26 @ (k1_relat_1 @ X26))
% 1.33/1.51          | (v1_partfun1 @ X26 @ (k1_relat_1 @ X26)))),
% 1.33/1.51      inference('simplify', [status(thm)], ['205'])).
% 1.33/1.51  thf('207', plain,
% 1.33/1.51      (![X0 : $i]:
% 1.33/1.51         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.33/1.51          | ~ (v1_relat_1 @ X0)
% 1.33/1.51          | ~ (v1_funct_1 @ X0)
% 1.33/1.51          | ~ (v2_funct_1 @ X0)
% 1.33/1.51          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.33/1.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['204', '206'])).
% 1.33/1.51  thf('208', plain,
% 1.33/1.51      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.33/1.51        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.33/1.51        | ~ (v2_funct_1 @ sk_C)
% 1.33/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.33/1.51        | ~ (v1_relat_1 @ sk_C))),
% 1.33/1.51      inference('sup-', [status(thm)], ['203', '207'])).
% 1.33/1.51  thf('209', plain,
% 1.33/1.51      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.33/1.51        (k1_zfmisc_1 @ 
% 1.33/1.51         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.33/1.51      inference('simplify', [status(thm)], ['117'])).
% 1.33/1.51  thf('210', plain,
% 1.33/1.51      (![X0 : $i, X1 : $i]:
% 1.33/1.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.33/1.51          | (v1_relat_1 @ X0)
% 1.33/1.51          | ~ (v1_relat_1 @ X1))),
% 1.33/1.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.33/1.51  thf('211', plain,
% 1.33/1.51      ((~ (v1_relat_1 @ 
% 1.33/1.51           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 1.33/1.51        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['209', '210'])).
% 1.33/1.51  thf('212', plain,
% 1.33/1.51      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.33/1.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.33/1.51  thf('213', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['211', '212'])).
% 1.33/1.51  thf('214', plain, ((v2_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('216', plain, ((v1_relat_1 @ sk_C)),
% 1.33/1.51      inference('demod', [status(thm)], ['41', '42'])).
% 1.33/1.51  thf('217', plain,
% 1.33/1.51      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.33/1.51      inference('demod', [status(thm)], ['208', '213', '214', '215', '216'])).
% 1.33/1.51  thf('218', plain,
% 1.33/1.51      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.33/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.33/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.33/1.51        | ~ (v2_funct_1 @ sk_C))),
% 1.33/1.51      inference('sup+', [status(thm)], ['200', '217'])).
% 1.33/1.51  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 1.33/1.51      inference('demod', [status(thm)], ['41', '42'])).
% 1.33/1.51  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('221', plain, ((v2_funct_1 @ sk_C)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('222', plain,
% 1.33/1.51      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 1.33/1.51  thf('223', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('224', plain,
% 1.33/1.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.33/1.51        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C)))),
% 1.33/1.51      inference('demod', [status(thm)], ['198', '199', '222', '223'])).
% 1.33/1.51  thf('225', plain,
% 1.33/1.51      (![X0 : $i]:
% 1.33/1.51         ((zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)
% 1.33/1.51          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.33/1.51      inference('sup-', [status(thm)], ['193', '224'])).
% 1.33/1.51  thf('226', plain,
% 1.33/1.51      (![X0 : $i]:
% 1.33/1.51         ((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.33/1.51          | ~ (l1_struct_0 @ sk_B)
% 1.33/1.51          | (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0))),
% 1.33/1.51      inference('sup+', [status(thm)], ['190', '225'])).
% 1.33/1.51  thf('227', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('228', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('229', plain,
% 1.33/1.51      (![X0 : $i]:
% 1.33/1.51         ((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.33/1.51          | (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0))),
% 1.33/1.51      inference('demod', [status(thm)], ['226', '227', '228'])).
% 1.33/1.51  thf('230', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('clc', [status(thm)], ['33', '34'])).
% 1.33/1.51  thf('231', plain, (![X0 : $i]: (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)),
% 1.33/1.51      inference('clc', [status(thm)], ['229', '230'])).
% 1.33/1.51  thf('232', plain,
% 1.33/1.51      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.33/1.51        (u1_struct_0 @ sk_B))),
% 1.33/1.51      inference('demod', [status(thm)], ['189', '231'])).
% 1.33/1.51  thf('233', plain,
% 1.33/1.51      (((u1_struct_0 @ sk_B)
% 1.33/1.51         = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.33/1.51            (k2_funct_1 @ sk_C)))),
% 1.33/1.51      inference('demod', [status(thm)], ['173', '232'])).
% 1.33/1.51  thf('234', plain, (((u1_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['149', '233'])).
% 1.33/1.51  thf('235', plain,
% 1.33/1.51      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup-', [status(thm)], ['0', '234'])).
% 1.33/1.51  thf('236', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.33/1.51      inference('sup+', [status(thm)], ['14', '15'])).
% 1.33/1.51  thf('237', plain, ((l1_struct_0 @ sk_B)),
% 1.33/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.51  thf('238', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 1.33/1.51      inference('demod', [status(thm)], ['235', '236', '237'])).
% 1.33/1.51  thf('239', plain, ($false), inference('simplify', [status(thm)], ['238'])).
% 1.33/1.51  
% 1.33/1.51  % SZS output end Refutation
% 1.33/1.51  
% 1.33/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
