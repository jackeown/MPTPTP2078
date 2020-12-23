%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:37 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 363 expanded)
%              Number of leaves         :   40 ( 138 expanded)
%              Depth                    :    8
%              Number of atoms          :  226 ( 940 expanded)
%              Number of equality atoms :   51 ( 183 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1552,plain,(
    ! [A_297,B_298,C_299,D_300] :
      ( k7_relset_1(A_297,B_298,C_299,D_300) = k9_relat_1(C_299,D_300)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1563,plain,(
    ! [D_301] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_301) = k9_relat_1('#skF_5',D_301) ),
    inference(resolution,[status(thm)],[c_54,c_1552])).

tff(c_32,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( m1_subset_1(k7_relset_1(A_28,B_29,C_30,D_31),k1_zfmisc_1(B_29))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1569,plain,(
    ! [D_301] :
      ( m1_subset_1(k9_relat_1('#skF_5',D_301),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1563,c_32])).

tff(c_1597,plain,(
    ! [D_302] : m1_subset_1(k9_relat_1('#skF_5',D_302),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1569])).

tff(c_10,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1606,plain,(
    ! [A_9,D_302] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_9,k9_relat_1('#skF_5',D_302)) ) ),
    inference(resolution,[status(thm)],[c_1597,c_10])).

tff(c_1609,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1606])).

tff(c_14,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_72])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_75])).

tff(c_1559,plain,(
    ! [D_300] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_300) = k9_relat_1('#skF_5',D_300) ),
    inference(resolution,[status(thm)],[c_54,c_1552])).

tff(c_52,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1562,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1559,c_52])).

tff(c_1468,plain,(
    ! [A_272,B_273,C_274] :
      ( r2_hidden('#skF_1'(A_272,B_273,C_274),B_273)
      | ~ r2_hidden(A_272,k9_relat_1(C_274,B_273))
      | ~ v1_relat_1(C_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    ! [F_46] :
      ( k1_funct_1('#skF_5',F_46) != '#skF_6'
      | ~ r2_hidden(F_46,'#skF_4')
      | ~ m1_subset_1(F_46,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1479,plain,(
    ! [A_272,C_274] :
      ( k1_funct_1('#skF_5','#skF_1'(A_272,'#skF_4',C_274)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_272,'#skF_4',C_274),'#skF_2')
      | ~ r2_hidden(A_272,k9_relat_1(C_274,'#skF_4'))
      | ~ v1_relat_1(C_274) ) ),
    inference(resolution,[status(thm)],[c_1468,c_50])).

tff(c_1579,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1562,c_1479])).

tff(c_1590,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1579])).

tff(c_1638,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1590])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1451,plain,(
    ! [A_265,B_266,C_267] :
      ( k1_relset_1(A_265,B_266,C_267) = k1_relat_1(C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1455,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1451])).

tff(c_1988,plain,(
    ! [B_363,A_364,C_365] :
      ( k1_xboole_0 = B_363
      | k1_relset_1(A_364,B_363,C_365) = A_364
      | ~ v1_funct_2(C_365,A_364,B_363)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(A_364,B_363))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2003,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1988])).

tff(c_2009,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1455,c_2003])).

tff(c_2010,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2009])).

tff(c_1639,plain,(
    ! [A_311,B_312,C_313] :
      ( r2_hidden('#skF_1'(A_311,B_312,C_313),k1_relat_1(C_313))
      | ~ r2_hidden(A_311,k9_relat_1(C_313,B_312))
      | ~ v1_relat_1(C_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1647,plain,(
    ! [A_311,B_312,C_313] :
      ( m1_subset_1('#skF_1'(A_311,B_312,C_313),k1_relat_1(C_313))
      | ~ r2_hidden(A_311,k9_relat_1(C_313,B_312))
      | ~ v1_relat_1(C_313) ) ),
    inference(resolution,[status(thm)],[c_1639,c_4])).

tff(c_2015,plain,(
    ! [A_311,B_312] :
      ( m1_subset_1('#skF_1'(A_311,B_312,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_311,k9_relat_1('#skF_5',B_312))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2010,c_1647])).

tff(c_2036,plain,(
    ! [A_369,B_370] :
      ( m1_subset_1('#skF_1'(A_369,B_370,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_369,k9_relat_1('#skF_5',B_370)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2015])).

tff(c_2047,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1562,c_2036])).

tff(c_2061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1638,c_2047])).

tff(c_2062,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2009])).

tff(c_187,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k7_relset_1(A_95,B_96,C_97,D_98) = k9_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_190,plain,(
    ! [D_98] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_98) = k9_relat_1('#skF_5',D_98) ),
    inference(resolution,[status(thm)],[c_54,c_187])).

tff(c_193,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_52])).

tff(c_128,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden('#skF_1'(A_77,B_78,C_79),B_78)
      | ~ r2_hidden(A_77,k9_relat_1(C_79,B_78))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_139,plain,(
    ! [A_77,C_79] :
      ( k1_funct_1('#skF_5','#skF_1'(A_77,'#skF_4',C_79)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_77,'#skF_4',C_79),'#skF_2')
      | ~ r2_hidden(A_77,k9_relat_1(C_79,'#skF_4'))
      | ~ v1_relat_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_128,c_50])).

tff(c_205,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_139])).

tff(c_214,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_205])).

tff(c_232,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_113,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_117,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_113])).

tff(c_631,plain,(
    ! [B_160,A_161,C_162] :
      ( k1_xboole_0 = B_160
      | k1_relset_1(A_161,B_160,C_162) = A_161
      | ~ v1_funct_2(C_162,A_161,B_160)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_646,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_631])).

tff(c_652,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117,c_646])).

tff(c_653,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_299,plain,(
    ! [A_116,B_117,C_118] :
      ( r2_hidden('#skF_1'(A_116,B_117,C_118),k1_relat_1(C_118))
      | ~ r2_hidden(A_116,k9_relat_1(C_118,B_117))
      | ~ v1_relat_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_307,plain,(
    ! [A_116,B_117,C_118] :
      ( m1_subset_1('#skF_1'(A_116,B_117,C_118),k1_relat_1(C_118))
      | ~ r2_hidden(A_116,k9_relat_1(C_118,B_117))
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_299,c_4])).

tff(c_658,plain,(
    ! [A_116,B_117] :
      ( m1_subset_1('#skF_1'(A_116,B_117,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_116,k9_relat_1('#skF_5',B_117))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_307])).

tff(c_678,plain,(
    ! [A_163,B_164] :
      ( m1_subset_1('#skF_1'(A_163,B_164,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_163,k9_relat_1('#skF_5',B_164)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_658])).

tff(c_689,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_193,c_678])).

tff(c_703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_689])).

tff(c_704,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | v1_xboole_0(B_58)
      | ~ m1_subset_1(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_93,plain,(
    ! [B_59,A_60] :
      ( ~ r1_tarski(B_59,A_60)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1(A_60,B_59) ) ),
    inference(resolution,[status(thm)],[c_79,c_30])).

tff(c_97,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_93])).

tff(c_102,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_717,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_102])).

tff(c_234,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( m1_subset_1(k7_relset_1(A_105,B_106,C_107,D_108),k1_zfmisc_1(B_106))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_255,plain,(
    ! [D_98] :
      ( m1_subset_1(k9_relat_1('#skF_5',D_98),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_234])).

tff(c_264,plain,(
    ! [D_109] : m1_subset_1(k9_relat_1('#skF_5',D_109),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_255])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_278,plain,(
    ! [A_112,D_113] :
      ( m1_subset_1(A_112,'#skF_3')
      | ~ r2_hidden(A_112,k9_relat_1('#skF_5',D_113)) ) ),
    inference(resolution,[status(thm)],[c_264,c_8])).

tff(c_290,plain,(
    m1_subset_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_193,c_278])).

tff(c_742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_717,c_290])).

tff(c_743,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_891,plain,(
    ! [A_197,B_198,C_199] :
      ( r2_hidden(k4_tarski('#skF_1'(A_197,B_198,C_199),A_197),C_199)
      | ~ r2_hidden(A_197,k9_relat_1(C_199,B_198))
      | ~ v1_relat_1(C_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [C_25,A_23,B_24] :
      ( k1_funct_1(C_25,A_23) = B_24
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1418,plain,(
    ! [C_257,A_258,B_259] :
      ( k1_funct_1(C_257,'#skF_1'(A_258,B_259,C_257)) = A_258
      | ~ v1_funct_1(C_257)
      | ~ r2_hidden(A_258,k9_relat_1(C_257,B_259))
      | ~ v1_relat_1(C_257) ) ),
    inference(resolution,[status(thm)],[c_891,c_26])).

tff(c_1428,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_1418])).

tff(c_1440,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_1428])).

tff(c_1442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_743,c_1440])).

tff(c_1443,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_2075,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2062,c_1443])).

tff(c_2078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1609,c_2075])).

tff(c_2079,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1590])).

tff(c_2173,plain,(
    ! [A_393,B_394,C_395] :
      ( r2_hidden(k4_tarski('#skF_1'(A_393,B_394,C_395),A_393),C_395)
      | ~ r2_hidden(A_393,k9_relat_1(C_395,B_394))
      | ~ v1_relat_1(C_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2630,plain,(
    ! [C_438,A_439,B_440] :
      ( k1_funct_1(C_438,'#skF_1'(A_439,B_440,C_438)) = A_439
      | ~ v1_funct_1(C_438)
      | ~ r2_hidden(A_439,k9_relat_1(C_438,B_440))
      | ~ v1_relat_1(C_438) ) ),
    inference(resolution,[status(thm)],[c_2173,c_26])).

tff(c_2640,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1562,c_2630])).

tff(c_2652,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58,c_2640])).

tff(c_2654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2079,c_2652])).

tff(c_2655,plain,(
    ! [A_9,D_302] : ~ r2_hidden(A_9,k9_relat_1('#skF_5',D_302)) ),
    inference(splitRight,[status(thm)],[c_1606])).

tff(c_2658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2655,c_1562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.86  
% 4.55/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.86  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.55/1.86  
% 4.55/1.86  %Foreground sorts:
% 4.55/1.86  
% 4.55/1.86  
% 4.55/1.86  %Background operators:
% 4.55/1.86  
% 4.55/1.86  
% 4.55/1.86  %Foreground operators:
% 4.55/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.55/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.86  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.55/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.86  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.55/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.55/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.55/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.55/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.86  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.55/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.55/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.55/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.55/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.55/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.86  
% 4.55/1.88  tff(f_134, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 4.55/1.88  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.55/1.88  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.55/1.88  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.55/1.88  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.55/1.88  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.55/1.88  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 4.55/1.88  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.55/1.88  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.55/1.88  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.55/1.88  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.55/1.88  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.55/1.88  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.55/1.88  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.55/1.88  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.55/1.88  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.55/1.88  tff(c_1552, plain, (![A_297, B_298, C_299, D_300]: (k7_relset_1(A_297, B_298, C_299, D_300)=k9_relat_1(C_299, D_300) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.55/1.88  tff(c_1563, plain, (![D_301]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_301)=k9_relat_1('#skF_5', D_301))), inference(resolution, [status(thm)], [c_54, c_1552])).
% 4.55/1.88  tff(c_32, plain, (![A_28, B_29, C_30, D_31]: (m1_subset_1(k7_relset_1(A_28, B_29, C_30, D_31), k1_zfmisc_1(B_29)) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.55/1.88  tff(c_1569, plain, (![D_301]: (m1_subset_1(k9_relat_1('#skF_5', D_301), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1563, c_32])).
% 4.55/1.88  tff(c_1597, plain, (![D_302]: (m1_subset_1(k9_relat_1('#skF_5', D_302), k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1569])).
% 4.55/1.88  tff(c_10, plain, (![C_11, B_10, A_9]: (~v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.55/1.88  tff(c_1606, plain, (![A_9, D_302]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_9, k9_relat_1('#skF_5', D_302)))), inference(resolution, [status(thm)], [c_1597, c_10])).
% 4.55/1.88  tff(c_1609, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1606])).
% 4.55/1.88  tff(c_14, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.55/1.88  tff(c_72, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.55/1.88  tff(c_75, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_72])).
% 4.55/1.88  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_75])).
% 4.55/1.88  tff(c_1559, plain, (![D_300]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_300)=k9_relat_1('#skF_5', D_300))), inference(resolution, [status(thm)], [c_54, c_1552])).
% 4.55/1.88  tff(c_52, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.55/1.88  tff(c_1562, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1559, c_52])).
% 4.55/1.88  tff(c_1468, plain, (![A_272, B_273, C_274]: (r2_hidden('#skF_1'(A_272, B_273, C_274), B_273) | ~r2_hidden(A_272, k9_relat_1(C_274, B_273)) | ~v1_relat_1(C_274))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.55/1.88  tff(c_50, plain, (![F_46]: (k1_funct_1('#skF_5', F_46)!='#skF_6' | ~r2_hidden(F_46, '#skF_4') | ~m1_subset_1(F_46, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.55/1.88  tff(c_1479, plain, (![A_272, C_274]: (k1_funct_1('#skF_5', '#skF_1'(A_272, '#skF_4', C_274))!='#skF_6' | ~m1_subset_1('#skF_1'(A_272, '#skF_4', C_274), '#skF_2') | ~r2_hidden(A_272, k9_relat_1(C_274, '#skF_4')) | ~v1_relat_1(C_274))), inference(resolution, [status(thm)], [c_1468, c_50])).
% 4.55/1.88  tff(c_1579, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1562, c_1479])).
% 4.55/1.88  tff(c_1590, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1579])).
% 4.55/1.88  tff(c_1638, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1590])).
% 4.55/1.88  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.55/1.88  tff(c_1451, plain, (![A_265, B_266, C_267]: (k1_relset_1(A_265, B_266, C_267)=k1_relat_1(C_267) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.55/1.88  tff(c_1455, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1451])).
% 4.55/1.88  tff(c_1988, plain, (![B_363, A_364, C_365]: (k1_xboole_0=B_363 | k1_relset_1(A_364, B_363, C_365)=A_364 | ~v1_funct_2(C_365, A_364, B_363) | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(A_364, B_363))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.55/1.88  tff(c_2003, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1988])).
% 4.55/1.88  tff(c_2009, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1455, c_2003])).
% 4.55/1.88  tff(c_2010, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_2009])).
% 4.55/1.88  tff(c_1639, plain, (![A_311, B_312, C_313]: (r2_hidden('#skF_1'(A_311, B_312, C_313), k1_relat_1(C_313)) | ~r2_hidden(A_311, k9_relat_1(C_313, B_312)) | ~v1_relat_1(C_313))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.55/1.88  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.55/1.88  tff(c_1647, plain, (![A_311, B_312, C_313]: (m1_subset_1('#skF_1'(A_311, B_312, C_313), k1_relat_1(C_313)) | ~r2_hidden(A_311, k9_relat_1(C_313, B_312)) | ~v1_relat_1(C_313))), inference(resolution, [status(thm)], [c_1639, c_4])).
% 4.55/1.88  tff(c_2015, plain, (![A_311, B_312]: (m1_subset_1('#skF_1'(A_311, B_312, '#skF_5'), '#skF_2') | ~r2_hidden(A_311, k9_relat_1('#skF_5', B_312)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2010, c_1647])).
% 4.55/1.88  tff(c_2036, plain, (![A_369, B_370]: (m1_subset_1('#skF_1'(A_369, B_370, '#skF_5'), '#skF_2') | ~r2_hidden(A_369, k9_relat_1('#skF_5', B_370)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2015])).
% 4.55/1.88  tff(c_2047, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_1562, c_2036])).
% 4.55/1.88  tff(c_2061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1638, c_2047])).
% 4.55/1.88  tff(c_2062, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2009])).
% 4.55/1.88  tff(c_187, plain, (![A_95, B_96, C_97, D_98]: (k7_relset_1(A_95, B_96, C_97, D_98)=k9_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.55/1.88  tff(c_190, plain, (![D_98]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_98)=k9_relat_1('#skF_5', D_98))), inference(resolution, [status(thm)], [c_54, c_187])).
% 4.55/1.88  tff(c_193, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_52])).
% 4.55/1.88  tff(c_128, plain, (![A_77, B_78, C_79]: (r2_hidden('#skF_1'(A_77, B_78, C_79), B_78) | ~r2_hidden(A_77, k9_relat_1(C_79, B_78)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.55/1.88  tff(c_139, plain, (![A_77, C_79]: (k1_funct_1('#skF_5', '#skF_1'(A_77, '#skF_4', C_79))!='#skF_6' | ~m1_subset_1('#skF_1'(A_77, '#skF_4', C_79), '#skF_2') | ~r2_hidden(A_77, k9_relat_1(C_79, '#skF_4')) | ~v1_relat_1(C_79))), inference(resolution, [status(thm)], [c_128, c_50])).
% 4.55/1.88  tff(c_205, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_193, c_139])).
% 4.55/1.88  tff(c_214, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_205])).
% 4.55/1.88  tff(c_232, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_214])).
% 4.55/1.88  tff(c_113, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.55/1.88  tff(c_117, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_113])).
% 4.55/1.88  tff(c_631, plain, (![B_160, A_161, C_162]: (k1_xboole_0=B_160 | k1_relset_1(A_161, B_160, C_162)=A_161 | ~v1_funct_2(C_162, A_161, B_160) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.55/1.88  tff(c_646, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_631])).
% 4.55/1.88  tff(c_652, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_117, c_646])).
% 4.55/1.88  tff(c_653, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_652])).
% 4.55/1.88  tff(c_299, plain, (![A_116, B_117, C_118]: (r2_hidden('#skF_1'(A_116, B_117, C_118), k1_relat_1(C_118)) | ~r2_hidden(A_116, k9_relat_1(C_118, B_117)) | ~v1_relat_1(C_118))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.55/1.88  tff(c_307, plain, (![A_116, B_117, C_118]: (m1_subset_1('#skF_1'(A_116, B_117, C_118), k1_relat_1(C_118)) | ~r2_hidden(A_116, k9_relat_1(C_118, B_117)) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_299, c_4])).
% 4.55/1.88  tff(c_658, plain, (![A_116, B_117]: (m1_subset_1('#skF_1'(A_116, B_117, '#skF_5'), '#skF_2') | ~r2_hidden(A_116, k9_relat_1('#skF_5', B_117)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_653, c_307])).
% 4.55/1.88  tff(c_678, plain, (![A_163, B_164]: (m1_subset_1('#skF_1'(A_163, B_164, '#skF_5'), '#skF_2') | ~r2_hidden(A_163, k9_relat_1('#skF_5', B_164)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_658])).
% 4.55/1.88  tff(c_689, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_193, c_678])).
% 4.55/1.88  tff(c_703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_689])).
% 4.55/1.88  tff(c_704, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_652])).
% 4.55/1.88  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.88  tff(c_79, plain, (![A_57, B_58]: (r2_hidden(A_57, B_58) | v1_xboole_0(B_58) | ~m1_subset_1(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.55/1.88  tff(c_30, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.55/1.88  tff(c_93, plain, (![B_59, A_60]: (~r1_tarski(B_59, A_60) | v1_xboole_0(B_59) | ~m1_subset_1(A_60, B_59))), inference(resolution, [status(thm)], [c_79, c_30])).
% 4.55/1.88  tff(c_97, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_93])).
% 4.55/1.88  tff(c_102, plain, (![A_1]: (~m1_subset_1(A_1, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_97])).
% 4.55/1.88  tff(c_717, plain, (![A_1]: (~m1_subset_1(A_1, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_102])).
% 4.55/1.88  tff(c_234, plain, (![A_105, B_106, C_107, D_108]: (m1_subset_1(k7_relset_1(A_105, B_106, C_107, D_108), k1_zfmisc_1(B_106)) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.55/1.88  tff(c_255, plain, (![D_98]: (m1_subset_1(k9_relat_1('#skF_5', D_98), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_190, c_234])).
% 4.55/1.88  tff(c_264, plain, (![D_109]: (m1_subset_1(k9_relat_1('#skF_5', D_109), k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_255])).
% 4.55/1.88  tff(c_8, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.55/1.88  tff(c_278, plain, (![A_112, D_113]: (m1_subset_1(A_112, '#skF_3') | ~r2_hidden(A_112, k9_relat_1('#skF_5', D_113)))), inference(resolution, [status(thm)], [c_264, c_8])).
% 4.55/1.88  tff(c_290, plain, (m1_subset_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_193, c_278])).
% 4.55/1.88  tff(c_742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_717, c_290])).
% 4.55/1.88  tff(c_743, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_214])).
% 4.55/1.88  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.55/1.88  tff(c_891, plain, (![A_197, B_198, C_199]: (r2_hidden(k4_tarski('#skF_1'(A_197, B_198, C_199), A_197), C_199) | ~r2_hidden(A_197, k9_relat_1(C_199, B_198)) | ~v1_relat_1(C_199))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.55/1.88  tff(c_26, plain, (![C_25, A_23, B_24]: (k1_funct_1(C_25, A_23)=B_24 | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.55/1.88  tff(c_1418, plain, (![C_257, A_258, B_259]: (k1_funct_1(C_257, '#skF_1'(A_258, B_259, C_257))=A_258 | ~v1_funct_1(C_257) | ~r2_hidden(A_258, k9_relat_1(C_257, B_259)) | ~v1_relat_1(C_257))), inference(resolution, [status(thm)], [c_891, c_26])).
% 4.55/1.88  tff(c_1428, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_193, c_1418])).
% 4.55/1.88  tff(c_1440, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_1428])).
% 4.55/1.88  tff(c_1442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_743, c_1440])).
% 4.55/1.88  tff(c_1443, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_97])).
% 4.55/1.88  tff(c_2075, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2062, c_1443])).
% 4.55/1.88  tff(c_2078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1609, c_2075])).
% 4.55/1.88  tff(c_2079, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_1590])).
% 4.55/1.88  tff(c_2173, plain, (![A_393, B_394, C_395]: (r2_hidden(k4_tarski('#skF_1'(A_393, B_394, C_395), A_393), C_395) | ~r2_hidden(A_393, k9_relat_1(C_395, B_394)) | ~v1_relat_1(C_395))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.55/1.88  tff(c_2630, plain, (![C_438, A_439, B_440]: (k1_funct_1(C_438, '#skF_1'(A_439, B_440, C_438))=A_439 | ~v1_funct_1(C_438) | ~r2_hidden(A_439, k9_relat_1(C_438, B_440)) | ~v1_relat_1(C_438))), inference(resolution, [status(thm)], [c_2173, c_26])).
% 4.55/1.88  tff(c_2640, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1562, c_2630])).
% 4.55/1.88  tff(c_2652, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58, c_2640])).
% 4.55/1.88  tff(c_2654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2079, c_2652])).
% 4.55/1.88  tff(c_2655, plain, (![A_9, D_302]: (~r2_hidden(A_9, k9_relat_1('#skF_5', D_302)))), inference(splitRight, [status(thm)], [c_1606])).
% 4.55/1.88  tff(c_2658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2655, c_1562])).
% 4.55/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.88  
% 4.55/1.88  Inference rules
% 4.55/1.88  ----------------------
% 4.55/1.88  #Ref     : 0
% 4.55/1.88  #Sup     : 525
% 4.55/1.88  #Fact    : 0
% 4.55/1.88  #Define  : 0
% 4.55/1.88  #Split   : 31
% 4.55/1.88  #Chain   : 0
% 4.55/1.88  #Close   : 0
% 4.55/1.88  
% 4.55/1.88  Ordering : KBO
% 4.55/1.88  
% 4.55/1.88  Simplification rules
% 4.55/1.88  ----------------------
% 4.55/1.88  #Subsume      : 46
% 4.55/1.88  #Demod        : 149
% 4.55/1.88  #Tautology    : 54
% 4.55/1.88  #SimpNegUnit  : 18
% 4.55/1.88  #BackRed      : 40
% 4.55/1.88  
% 4.55/1.88  #Partial instantiations: 0
% 4.55/1.88  #Strategies tried      : 1
% 4.55/1.88  
% 4.55/1.88  Timing (in seconds)
% 4.55/1.88  ----------------------
% 4.55/1.88  Preprocessing        : 0.33
% 4.55/1.88  Parsing              : 0.17
% 4.55/1.88  CNF conversion       : 0.02
% 4.55/1.88  Main loop            : 0.72
% 4.55/1.88  Inferencing          : 0.26
% 4.55/1.88  Reduction            : 0.20
% 4.55/1.88  Demodulation         : 0.14
% 4.55/1.88  BG Simplification    : 0.04
% 4.55/1.88  Subsumption          : 0.15
% 4.55/1.88  Abstraction          : 0.04
% 4.55/1.88  MUC search           : 0.00
% 4.55/1.88  Cooper               : 0.00
% 4.55/1.88  Total                : 1.09
% 4.55/1.88  Index Insertion      : 0.00
% 4.55/1.88  Index Deletion       : 0.00
% 4.55/1.88  Index Matching       : 0.00
% 4.55/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
