%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NZkwK7NLgF

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:58 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 783 expanded)
%              Number of leaves         :   40 ( 244 expanded)
%              Depth                    :   27
%              Number of atoms          : 2147 (19633 expanded)
%              Number of equality atoms :  138 (1027 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('26',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

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

thf('38',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X38 @ X40 )
       != X38 )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_tops_2 @ X39 @ X38 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('64',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40','51','52','64'])).

thf('66',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','66'])).

thf('68',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('69',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('70',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('76',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( v1_partfun1 @ X31 @ X32 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','83'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('88',plain,(
    ! [X37: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['86','93'])).

thf('95',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('98',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_partfun1 @ X35 @ X34 )
      | ( ( k1_relat_1 @ X35 )
        = X34 )
      | ~ ( v4_relat_1 @ X35 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('101',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('103',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('106',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('107',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','104','107'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('109',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('110',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('111',plain,(
    ! [X17: $i] :
      ( ( r1_tarski @ X17 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('112',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['108','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('122',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('123',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['69','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('130',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('131',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('132',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('133',plain,(
    ! [X36: $i] :
      ( ( ( k2_struct_0 @ X36 )
        = ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('134',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('135',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('139',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['131','140'])).

thf('142',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','143'])).

thf('145',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('150',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','150'])).

thf('152',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','151'])).

thf('153',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('160',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['158','159'])).

thf('161',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['67','160'])).

thf('162',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('163',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('164',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('165',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['162','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['166','167','168','169'])).

thf('171',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['161','170'])).

thf('172',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','171'])).

thf('173',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','104','107'])).

thf('174',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['172','173','174','175','176'])).

thf('178',plain,(
    $false ),
    inference(simplify,[status(thm)],['177'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NZkwK7NLgF
% 0.16/0.38  % Computer   : n004.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 20:56:09 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 522 iterations in 0.248s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.74  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.74  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.55/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.74  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.55/0.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.55/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.55/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.74  thf(t55_funct_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.74       ( ( v2_funct_1 @ A ) =>
% 0.55/0.74         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.55/0.74           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (![X21 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X21)
% 0.55/0.74          | ((k1_relat_1 @ X21) = (k2_relat_1 @ (k2_funct_1 @ X21)))
% 0.55/0.74          | ~ (v1_funct_1 @ X21)
% 0.55/0.74          | ~ (v1_relat_1 @ X21))),
% 0.55/0.74      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.74  thf(t62_tops_2, conjecture,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_struct_0 @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.74                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74                 ( m1_subset_1 @
% 0.55/0.74                   C @ 
% 0.55/0.74                   ( k1_zfmisc_1 @
% 0.55/0.74                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.74               ( ( ( ( k2_relset_1 @
% 0.55/0.74                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.74                     ( k2_struct_0 @ B ) ) & 
% 0.55/0.74                   ( v2_funct_1 @ C ) ) =>
% 0.55/0.74                 ( ( ( k1_relset_1 @
% 0.55/0.74                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.74                       ( k2_tops_2 @
% 0.55/0.74                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.55/0.74                     ( k2_struct_0 @ B ) ) & 
% 0.55/0.74                   ( ( k2_relset_1 @
% 0.55/0.74                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.74                       ( k2_tops_2 @
% 0.55/0.74                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.55/0.74                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i]:
% 0.55/0.74        ( ( l1_struct_0 @ A ) =>
% 0.55/0.74          ( ![B:$i]:
% 0.55/0.74            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.55/0.74              ( ![C:$i]:
% 0.55/0.74                ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.74                    ( v1_funct_2 @
% 0.55/0.74                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74                    ( m1_subset_1 @
% 0.55/0.74                      C @ 
% 0.55/0.74                      ( k1_zfmisc_1 @
% 0.55/0.74                        ( k2_zfmisc_1 @
% 0.55/0.74                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.74                  ( ( ( ( k2_relset_1 @
% 0.55/0.74                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.74                        ( k2_struct_0 @ B ) ) & 
% 0.55/0.74                      ( v2_funct_1 @ C ) ) =>
% 0.55/0.74                    ( ( ( k1_relset_1 @
% 0.55/0.74                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.74                          ( k2_tops_2 @
% 0.55/0.74                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.55/0.74                        ( k2_struct_0 @ B ) ) & 
% 0.55/0.74                      ( ( k2_relset_1 @
% 0.55/0.74                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.74                          ( k2_tops_2 @
% 0.55/0.74                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.55/0.74                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(redefinition_k2_relset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.74       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.74         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.55/0.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74         = (k2_relat_1 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74         = (k2_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('5', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.74  thf(d3_struct_0, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (![X36 : $i]:
% 0.55/0.74         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X36 : $i]:
% 0.55/0.74         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      (![X36 : $i]:
% 0.55/0.74         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.74  thf('9', plain,
% 0.55/0.74      (![X36 : $i]:
% 0.55/0.74         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74          != (k2_struct_0 @ sk_B))
% 0.55/0.74        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74            != (k2_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74          != (k2_struct_0 @ sk_A)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74                = (k2_struct_0 @ sk_A))))),
% 0.55/0.74      inference('split', [status(esa)], ['10'])).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74           != (k2_struct_0 @ sk_A))
% 0.55/0.74         | ~ (l1_struct_0 @ sk_B)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74                = (k2_struct_0 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['9', '11'])).
% 0.55/0.74  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74          != (k2_struct_0 @ sk_A)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74                = (k2_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['12', '13'])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.74           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74           != (k2_struct_0 @ sk_A))
% 0.55/0.74         | ~ (l1_struct_0 @ sk_A)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74                = (k2_struct_0 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['8', '14'])).
% 0.55/0.74  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74          != (k2_struct_0 @ sk_A)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74                = (k2_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['15', '16'])).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.74           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74           != (k2_struct_0 @ sk_A))
% 0.55/0.74         | ~ (l1_struct_0 @ sk_A)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74                = (k2_struct_0 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['7', '17'])).
% 0.55/0.74  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.74          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74          != (k2_struct_0 @ sk_A)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74                = (k2_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.74  thf('21', plain,
% 0.55/0.74      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.74           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74           != (k2_struct_0 @ sk_A))
% 0.55/0.74         | ~ (l1_struct_0 @ sk_B)))
% 0.55/0.74         <= (~
% 0.55/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74                = (k2_struct_0 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['6', '20'])).
% 0.55/0.74  thf('22', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.74          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.55/0.74          != (k2_struct_0 @ sk_A)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.55/0.75  thf('24', plain,
% 0.55/0.75      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75          != (k2_struct_0 @ sk_A)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_A))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['5', '23'])).
% 0.55/0.75  thf('25', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf('26', plain,
% 0.55/0.75      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.55/0.75          != (k2_struct_0 @ sk_A)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['24', '25'])).
% 0.55/0.75  thf('27', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('28', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('29', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('30', plain,
% 0.55/0.75      (((m1_subset_1 @ sk_C @ 
% 0.55/0.75         (k1_zfmisc_1 @ 
% 0.55/0.75          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['28', '29'])).
% 0.55/0.75  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('32', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['30', '31'])).
% 0.55/0.75  thf('33', plain,
% 0.55/0.75      (((m1_subset_1 @ sk_C @ 
% 0.55/0.75         (k1_zfmisc_1 @ 
% 0.55/0.75          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['27', '32'])).
% 0.55/0.75  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('35', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['33', '34'])).
% 0.55/0.75  thf('36', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf('37', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.55/0.75      inference('demod', [status(thm)], ['35', '36'])).
% 0.55/0.75  thf(d4_tops_2, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.75       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.55/0.75         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.55/0.75  thf('38', plain,
% 0.55/0.75      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.55/0.75         (((k2_relset_1 @ X39 @ X38 @ X40) != (X38))
% 0.55/0.75          | ~ (v2_funct_1 @ X40)
% 0.55/0.75          | ((k2_tops_2 @ X39 @ X38 @ X40) = (k2_funct_1 @ X40))
% 0.55/0.75          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 0.55/0.75          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.55/0.75          | ~ (v1_funct_1 @ X40))),
% 0.55/0.75      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.55/0.75  thf('39', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.55/0.75        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.75            = (k2_funct_1 @ sk_C))
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.75        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.75            != (k2_relat_1 @ sk_C)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['37', '38'])).
% 0.55/0.75  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('41', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('42', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('43', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('44', plain,
% 0.55/0.75      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['42', '43'])).
% 0.55/0.75  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('46', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['44', '45'])).
% 0.55/0.75  thf('47', plain,
% 0.55/0.75      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['41', '46'])).
% 0.55/0.75  thf('48', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('49', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['47', '48'])).
% 0.55/0.75  thf('50', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf('51', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.75  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('53', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('54', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('55', plain,
% 0.55/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('56', plain,
% 0.55/0.75      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75          = (k2_struct_0 @ sk_B))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['54', '55'])).
% 0.55/0.75  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('58', plain,
% 0.55/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.55/0.75  thf('59', plain,
% 0.55/0.75      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75          = (k2_struct_0 @ sk_B))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['53', '58'])).
% 0.55/0.75  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('61', plain,
% 0.55/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['59', '60'])).
% 0.55/0.75  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf('63', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf('64', plain,
% 0.55/0.75      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.75         = (k2_relat_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.55/0.75  thf('65', plain,
% 0.55/0.75      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.75          = (k2_funct_1 @ sk_C))
% 0.55/0.75        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['39', '40', '51', '52', '64'])).
% 0.55/0.75  thf('66', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['65'])).
% 0.55/0.75  thf('67', plain,
% 0.55/0.75      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['26', '66'])).
% 0.55/0.75  thf('68', plain,
% 0.55/0.75      (![X21 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X21)
% 0.55/0.75          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 0.55/0.75          | ~ (v1_funct_1 @ X21)
% 0.55/0.75          | ~ (v1_relat_1 @ X21))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('69', plain,
% 0.55/0.75      (![X21 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X21)
% 0.55/0.75          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 0.55/0.75          | ~ (v1_funct_1 @ X21)
% 0.55/0.75          | ~ (v1_relat_1 @ X21))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('70', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('71', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('72', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('73', plain,
% 0.55/0.75      (((m1_subset_1 @ sk_C @ 
% 0.55/0.75         (k1_zfmisc_1 @ 
% 0.55/0.75          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['71', '72'])).
% 0.55/0.75  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('75', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['73', '74'])).
% 0.55/0.75  thf(cc5_funct_2, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.55/0.75       ( ![C:$i]:
% 0.55/0.75         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.55/0.75             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.55/0.75  thf('76', plain,
% 0.55/0.75      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.75         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.55/0.75          | (v1_partfun1 @ X31 @ X32)
% 0.55/0.75          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.55/0.75          | ~ (v1_funct_1 @ X31)
% 0.55/0.75          | (v1_xboole_0 @ X33))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.55/0.75  thf('77', plain,
% 0.55/0.75      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.55/0.75        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['75', '76'])).
% 0.55/0.75  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('79', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('80', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('81', plain,
% 0.55/0.75      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['79', '80'])).
% 0.55/0.75  thf('82', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('83', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['81', '82'])).
% 0.55/0.75  thf('84', plain,
% 0.55/0.75      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.55/0.75        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)], ['77', '78', '83'])).
% 0.55/0.75  thf('85', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf('86', plain,
% 0.55/0.75      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.55/0.75        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)], ['84', '85'])).
% 0.55/0.75  thf('87', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf(fc5_struct_0, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.55/0.75       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.55/0.75  thf('88', plain,
% 0.55/0.75      (![X37 : $i]:
% 0.55/0.75         (~ (v1_xboole_0 @ (k2_struct_0 @ X37))
% 0.55/0.75          | ~ (l1_struct_0 @ X37)
% 0.55/0.75          | (v2_struct_0 @ X37))),
% 0.55/0.75      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.55/0.75  thf('89', plain,
% 0.55/0.75      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.55/0.75        | (v2_struct_0 @ sk_B)
% 0.55/0.75        | ~ (l1_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['87', '88'])).
% 0.55/0.75  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('91', plain,
% 0.55/0.75      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['89', '90'])).
% 0.55/0.75  thf('92', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('93', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.55/0.75      inference('clc', [status(thm)], ['91', '92'])).
% 0.55/0.75  thf('94', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.55/0.75      inference('clc', [status(thm)], ['86', '93'])).
% 0.55/0.75  thf('95', plain,
% 0.55/0.75      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['70', '94'])).
% 0.55/0.75  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('97', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['95', '96'])).
% 0.55/0.75  thf(d4_partfun1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.55/0.75       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.55/0.75  thf('98', plain,
% 0.55/0.75      (![X34 : $i, X35 : $i]:
% 0.55/0.75         (~ (v1_partfun1 @ X35 @ X34)
% 0.55/0.75          | ((k1_relat_1 @ X35) = (X34))
% 0.55/0.75          | ~ (v4_relat_1 @ X35 @ X34)
% 0.55/0.75          | ~ (v1_relat_1 @ X35))),
% 0.55/0.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.55/0.75  thf('99', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.55/0.75        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['97', '98'])).
% 0.55/0.75  thf('100', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(cc2_relat_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ A ) =>
% 0.55/0.75       ( ![B:$i]:
% 0.55/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.55/0.75  thf('101', plain,
% 0.55/0.75      (![X6 : $i, X7 : $i]:
% 0.55/0.75         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.55/0.75          | (v1_relat_1 @ X6)
% 0.55/0.75          | ~ (v1_relat_1 @ X7))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.75  thf('102', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ 
% 0.55/0.75           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.55/0.75        | (v1_relat_1 @ sk_C))),
% 0.55/0.75      inference('sup-', [status(thm)], ['100', '101'])).
% 0.55/0.75  thf(fc6_relat_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.55/0.75  thf('103', plain,
% 0.55/0.75      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.55/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.75  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.55/0.75  thf('105', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['30', '31'])).
% 0.55/0.75  thf(cc2_relset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.55/0.75  thf('106', plain,
% 0.55/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.75         ((v4_relat_1 @ X22 @ X23)
% 0.55/0.75          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.75  thf('107', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup-', [status(thm)], ['105', '106'])).
% 0.55/0.75  thf('108', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '104', '107'])).
% 0.55/0.75  thf(dt_k2_funct_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.75       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.55/0.75         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.55/0.75  thf('109', plain,
% 0.55/0.75      (![X18 : $i]:
% 0.55/0.75         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 0.55/0.75          | ~ (v1_funct_1 @ X18)
% 0.55/0.75          | ~ (v1_relat_1 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.75  thf('110', plain,
% 0.55/0.75      (![X21 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X21)
% 0.55/0.75          | ((k1_relat_1 @ X21) = (k2_relat_1 @ (k2_funct_1 @ X21)))
% 0.55/0.75          | ~ (v1_funct_1 @ X21)
% 0.55/0.75          | ~ (v1_relat_1 @ X21))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf(t21_relat_1, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( v1_relat_1 @ A ) =>
% 0.55/0.75       ( r1_tarski @
% 0.55/0.75         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.55/0.75  thf('111', plain,
% 0.55/0.75      (![X17 : $i]:
% 0.55/0.75         ((r1_tarski @ X17 @ 
% 0.55/0.75           (k2_zfmisc_1 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.55/0.75          | ~ (v1_relat_1 @ X17))),
% 0.55/0.75      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.55/0.75  thf(t3_subset, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.55/0.75  thf('112', plain,
% 0.55/0.75      (![X3 : $i, X5 : $i]:
% 0.55/0.75         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.55/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.75  thf('113', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X0)
% 0.55/0.75          | (m1_subset_1 @ X0 @ 
% 0.55/0.75             (k1_zfmisc_1 @ 
% 0.55/0.75              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['111', '112'])).
% 0.55/0.75  thf('114', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))))
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['110', '113'])).
% 0.55/0.75  thf('115', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (v1_relat_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0)
% 0.55/0.75          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.55/0.75             (k1_zfmisc_1 @ 
% 0.55/0.75              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.55/0.75               (k1_relat_1 @ X0)))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['109', '114'])).
% 0.55/0.75  thf('116', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))))
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['115'])).
% 0.55/0.75  thf('117', plain,
% 0.55/0.75      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75         (k1_zfmisc_1 @ 
% 0.55/0.75          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75           (k2_struct_0 @ sk_A))))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup+', [status(thm)], ['108', '116'])).
% 0.55/0.75  thf('118', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.55/0.75  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('121', plain,
% 0.55/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75          (k2_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 0.55/0.75  thf(redefinition_k1_relset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.55/0.75  thf('122', plain,
% 0.55/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.75         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.55/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.55/0.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.55/0.75  thf('123', plain,
% 0.55/0.75      (((k1_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75         (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C))
% 0.55/0.75         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['121', '122'])).
% 0.55/0.75  thf('124', plain,
% 0.55/0.75      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup+', [status(thm)], ['69', '123'])).
% 0.55/0.75  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.55/0.75  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('128', plain,
% 0.55/0.75      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 0.55/0.75  thf('129', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['65'])).
% 0.55/0.75  thf('130', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('131', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('132', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('133', plain,
% 0.55/0.75      (![X36 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X36) = (u1_struct_0 @ X36)) | ~ (l1_struct_0 @ X36))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('134', plain,
% 0.55/0.75      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75          != (k2_struct_0 @ sk_B)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('split', [status(esa)], ['10'])).
% 0.55/0.75  thf('135', plain,
% 0.55/0.75      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75           != (k2_struct_0 @ sk_B))
% 0.55/0.75         | ~ (l1_struct_0 @ sk_B)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['133', '134'])).
% 0.55/0.75  thf('136', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('137', plain,
% 0.55/0.75      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75          != (k2_struct_0 @ sk_B)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['135', '136'])).
% 0.55/0.75  thf('138', plain,
% 0.55/0.75      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75           != (k2_struct_0 @ sk_B))
% 0.55/0.75         | ~ (l1_struct_0 @ sk_A)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['132', '137'])).
% 0.55/0.75  thf('139', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('140', plain,
% 0.55/0.75      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75          != (k2_struct_0 @ sk_B)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['138', '139'])).
% 0.55/0.75  thf('141', plain,
% 0.55/0.75      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75           != (k2_struct_0 @ sk_B))
% 0.55/0.75         | ~ (l1_struct_0 @ sk_A)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['131', '140'])).
% 0.55/0.75  thf('142', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('143', plain,
% 0.55/0.75      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75          != (k2_struct_0 @ sk_B)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['141', '142'])).
% 0.55/0.75  thf('144', plain,
% 0.55/0.75      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75           != (k2_struct_0 @ sk_B))
% 0.55/0.75         | ~ (l1_struct_0 @ sk_B)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['130', '143'])).
% 0.55/0.75  thf('145', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('146', plain,
% 0.55/0.75      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75          != (k2_struct_0 @ sk_B)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['144', '145'])).
% 0.55/0.75  thf('147', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf('148', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf('149', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.75  thf('150', plain,
% 0.55/0.75      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.55/0.75          != (k2_relat_1 @ sk_C)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 0.55/0.75  thf('151', plain,
% 0.55/0.75      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['129', '150'])).
% 0.55/0.75  thf('152', plain,
% 0.55/0.75      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['128', '151'])).
% 0.55/0.75  thf('153', plain,
% 0.55/0.75      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.55/0.75         | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75         | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75         | ~ (v2_funct_1 @ sk_C)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['68', '152'])).
% 0.55/0.75  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.55/0.75  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('157', plain,
% 0.55/0.75      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.55/0.75         <= (~
% 0.55/0.75             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75                = (k2_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 0.55/0.75  thf('158', plain,
% 0.55/0.75      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75          = (k2_struct_0 @ sk_B)))),
% 0.55/0.75      inference('simplify', [status(thm)], ['157'])).
% 0.55/0.75  thf('159', plain,
% 0.55/0.75      (~
% 0.55/0.75       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75          = (k2_struct_0 @ sk_A))) | 
% 0.55/0.75       ~
% 0.55/0.75       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75          = (k2_struct_0 @ sk_B)))),
% 0.55/0.75      inference('split', [status(esa)], ['10'])).
% 0.55/0.75  thf('160', plain,
% 0.55/0.75      (~
% 0.55/0.75       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75          = (k2_struct_0 @ sk_A)))),
% 0.55/0.75      inference('sat_resolution*', [status(thm)], ['158', '159'])).
% 0.55/0.75  thf('161', plain,
% 0.55/0.75      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('simpl_trail', [status(thm)], ['67', '160'])).
% 0.55/0.75  thf('162', plain,
% 0.55/0.75      (![X21 : $i]:
% 0.55/0.75         (~ (v2_funct_1 @ X21)
% 0.55/0.75          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 0.55/0.75          | ~ (v1_funct_1 @ X21)
% 0.55/0.75          | ~ (v1_relat_1 @ X21))),
% 0.55/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.55/0.75  thf('163', plain,
% 0.55/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75          (k2_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 0.55/0.75  thf('164', plain,
% 0.55/0.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.55/0.75         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.55/0.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.55/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.75  thf('165', plain,
% 0.55/0.75      (((k2_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75         (k2_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C))
% 0.55/0.75         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['163', '164'])).
% 0.55/0.75  thf('166', plain,
% 0.55/0.75      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup+', [status(thm)], ['162', '165'])).
% 0.55/0.75  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.55/0.75  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('170', plain,
% 0.55/0.75      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['166', '167', '168', '169'])).
% 0.55/0.75  thf('171', plain,
% 0.55/0.75      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['161', '170'])).
% 0.55/0.75  thf('172', plain,
% 0.55/0.75      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.55/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup-', [status(thm)], ['0', '171'])).
% 0.55/0.75  thf('173', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '104', '107'])).
% 0.55/0.75  thf('174', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.55/0.75  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('176', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('177', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['172', '173', '174', '175', '176'])).
% 0.55/0.75  thf('178', plain, ($false), inference('simplify', [status(thm)], ['177'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
