%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:37 EST 2020

% Result     : Theorem 19.19s
% Output     : CNFRefutation 19.19s
% Verified   : 
% Statistics : Number of formulae       :  208 (2947 expanded)
%              Number of leaves         :   43 ( 890 expanded)
%              Depth                    :   17
%              Number of atoms          :  348 (9529 expanded)
%              Number of equality atoms :   87 (3707 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_70,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_147,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_160,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_147])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56319,plain,(
    ! [A_1770,B_1771,C_1772] :
      ( k1_relset_1(A_1770,B_1771,C_1772) = k1_relat_1(C_1772)
      | ~ m1_subset_1(C_1772,k1_zfmisc_1(k2_zfmisc_1(A_1770,B_1771))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56338,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_56319])).

tff(c_57517,plain,(
    ! [B_1881,A_1882,C_1883] :
      ( k1_xboole_0 = B_1881
      | k1_relset_1(A_1882,B_1881,C_1883) = A_1882
      | ~ v1_funct_2(C_1883,A_1882,B_1881)
      | ~ m1_subset_1(C_1883,k1_zfmisc_1(k2_zfmisc_1(A_1882,B_1881))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_57530,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_57517])).

tff(c_57544,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_56338,c_57530])).

tff(c_57545,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_57544])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( k1_relat_1(k7_relat_1(B_20,A_19)) = A_19
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_57566,plain,(
    ! [A_19] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_19)) = A_19
      | ~ r1_tarski(A_19,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57545,c_32])).

tff(c_58163,plain,(
    ! [A_1906] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_1906)) = A_1906
      | ~ r1_tarski(A_1906,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_57566])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_57022,plain,(
    ! [A_1843,B_1844,C_1845,D_1846] :
      ( k2_partfun1(A_1843,B_1844,C_1845,D_1846) = k7_relat_1(C_1845,D_1846)
      | ~ m1_subset_1(C_1845,k1_zfmisc_1(k2_zfmisc_1(A_1843,B_1844)))
      | ~ v1_funct_1(C_1845) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_57029,plain,(
    ! [D_1846] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_1846) = k7_relat_1('#skF_5',D_1846)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_57022])).

tff(c_57040,plain,(
    ! [D_1846] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_1846) = k7_relat_1('#skF_5',D_1846) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_57029])).

tff(c_123,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_1'(A_58,B_59),A_58)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [A_58] : r1_tarski(A_58,A_58) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_3235,plain,(
    ! [A_339,B_340,C_341] :
      ( k1_relset_1(A_339,B_340,C_341) = k1_relat_1(C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3250,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_3235])).

tff(c_4665,plain,(
    ! [B_468,A_469,C_470] :
      ( k1_xboole_0 = B_468
      | k1_relset_1(A_469,B_468,C_470) = A_469
      | ~ v1_funct_2(C_470,A_469,B_468)
      | ~ m1_subset_1(C_470,k1_zfmisc_1(k2_zfmisc_1(A_469,B_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4675,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_4665])).

tff(c_4686,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3250,c_4675])).

tff(c_4687,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4686])).

tff(c_4720,plain,(
    ! [A_19] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_19)) = A_19
      | ~ r1_tarski(A_19,'#skF_2')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4687,c_32])).

tff(c_4763,plain,(
    ! [A_19] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_19)) = A_19
      | ~ r1_tarski(A_19,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_4720])).

tff(c_3983,plain,(
    ! [A_407,B_408,C_409,D_410] :
      ( k2_partfun1(A_407,B_408,C_409,D_410) = k7_relat_1(C_409,D_410)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(A_407,B_408)))
      | ~ v1_funct_1(C_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3988,plain,(
    ! [D_410] :
      ( k2_partfun1('#skF_2','#skF_3','#skF_5',D_410) = k7_relat_1('#skF_5',D_410)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_3983])).

tff(c_3996,plain,(
    ! [D_410] : k2_partfun1('#skF_2','#skF_3','#skF_5',D_410) = k7_relat_1('#skF_5',D_410) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3988])).

tff(c_4831,plain,(
    ! [A_473,B_474,C_475,D_476] :
      ( m1_subset_1(k2_partfun1(A_473,B_474,C_475,D_476),k1_zfmisc_1(k2_zfmisc_1(A_473,B_474)))
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474)))
      | ~ v1_funct_1(C_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4859,plain,(
    ! [D_410] :
      ( m1_subset_1(k7_relat_1('#skF_5',D_410),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3996,c_4831])).

tff(c_5098,plain,(
    ! [D_486] : m1_subset_1(k7_relat_1('#skF_5',D_486),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_4859])).

tff(c_38,plain,(
    ! [C_27,A_25,B_26] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5145,plain,(
    ! [D_486] : v1_relat_1(k7_relat_1('#skF_5',D_486)) ),
    inference(resolution,[status(thm)],[c_5098,c_38])).

tff(c_36,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_24,A_23)),k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2109,plain,(
    ! [B_252,A_253] :
      ( v5_relat_1(B_252,A_253)
      | ~ r1_tarski(k2_relat_1(B_252),A_253)
      | ~ v1_relat_1(B_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2117,plain,(
    ! [B_24,A_23] :
      ( v5_relat_1(k7_relat_1(B_24,A_23),k2_relat_1(B_24))
      | ~ v1_relat_1(k7_relat_1(B_24,A_23))
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_36,c_2109])).

tff(c_2088,plain,(
    ! [C_247,B_248,A_249] :
      ( v5_relat_1(C_247,B_248)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2103,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2088])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2296,plain,(
    ! [A_281,C_282,B_283] :
      ( r1_tarski(A_281,C_282)
      | ~ r1_tarski(B_283,C_282)
      | ~ r1_tarski(A_281,B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9052,plain,(
    ! [A_625,A_626,B_627] :
      ( r1_tarski(A_625,A_626)
      | ~ r1_tarski(A_625,k2_relat_1(B_627))
      | ~ v5_relat_1(B_627,A_626)
      | ~ v1_relat_1(B_627) ) ),
    inference(resolution,[status(thm)],[c_30,c_2296])).

tff(c_43642,plain,(
    ! [B_1494,A_1495,B_1496] :
      ( r1_tarski(k2_relat_1(B_1494),A_1495)
      | ~ v5_relat_1(B_1496,A_1495)
      | ~ v1_relat_1(B_1496)
      | ~ v5_relat_1(B_1494,k2_relat_1(B_1496))
      | ~ v1_relat_1(B_1494) ) ),
    inference(resolution,[status(thm)],[c_30,c_9052])).

tff(c_43762,plain,(
    ! [B_1494] :
      ( r1_tarski(k2_relat_1(B_1494),'#skF_3')
      | ~ v1_relat_1('#skF_5')
      | ~ v5_relat_1(B_1494,k2_relat_1('#skF_5'))
      | ~ v1_relat_1(B_1494) ) ),
    inference(resolution,[status(thm)],[c_2103,c_43642])).

tff(c_43893,plain,(
    ! [B_1497] :
      ( r1_tarski(k2_relat_1(B_1497),'#skF_3')
      | ~ v5_relat_1(B_1497,k2_relat_1('#skF_5'))
      | ~ v1_relat_1(B_1497) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_43762])).

tff(c_44023,plain,(
    ! [A_23] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_23)),'#skF_3')
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_23))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2117,c_43893])).

tff(c_44136,plain,(
    ! [A_23] : r1_tarski(k2_relat_1(k7_relat_1('#skF_5',A_23)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_5145,c_44023])).

tff(c_4198,plain,(
    ! [C_429,A_430,B_431] :
      ( m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431)))
      | ~ r1_tarski(k2_relat_1(C_429),B_431)
      | ~ r1_tarski(k1_relat_1(C_429),A_430)
      | ~ v1_relat_1(C_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1995,plain,(
    ! [A_227,B_228,C_229,D_230] :
      ( v1_funct_1(k2_partfun1(A_227,B_228,C_229,D_230))
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | ~ v1_funct_1(C_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2000,plain,(
    ! [D_230] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_230))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_1995])).

tff(c_2008,plain,(
    ! [D_230] : v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5',D_230)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2000])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_161,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_2011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_161])).

tff(c_2012,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2020,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2012])).

tff(c_3999,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3996,c_2020])).

tff(c_4227,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4198,c_3999])).

tff(c_55006,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5145,c_44136,c_4227])).

tff(c_55021,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4763,c_55006])).

tff(c_55040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_128,c_55021])).

tff(c_55041,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2012])).

tff(c_57048,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57040,c_55041])).

tff(c_55042,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2012])).

tff(c_57047,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57040,c_55042])).

tff(c_44,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_relset_1(A_31,B_32,C_33) = k1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_57133,plain,(
    k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) = k1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_57047,c_44])).

tff(c_57261,plain,(
    ! [B_1856,C_1857,A_1858] :
      ( k1_xboole_0 = B_1856
      | v1_funct_2(C_1857,A_1858,B_1856)
      | k1_relset_1(A_1858,B_1856,C_1857) != A_1858
      | ~ m1_subset_1(C_1857,k1_zfmisc_1(k2_zfmisc_1(A_1858,B_1856))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_57267,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_57047,c_57261])).

tff(c_57283,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_4'),'#skF_4','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57133,c_57267])).

tff(c_57284,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_57048,c_82,c_57283])).

tff(c_58172,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58163,c_57284])).

tff(c_58253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_58172])).

tff(c_58255,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_58254,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_58261,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58255,c_58254])).

tff(c_58268,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58261,c_70])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58300,plain,(
    ! [A_1910] :
      ( A_1910 = '#skF_3'
      | ~ r1_tarski(A_1910,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58255,c_58255,c_12])).

tff(c_58308,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58268,c_58300])).

tff(c_18,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_58283,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_3',B_12) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58255,c_58255,c_18])).

tff(c_61250,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_4',B_12) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58308,c_58283])).

tff(c_58266,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58261,c_72])).

tff(c_61264,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58308,c_58266])).

tff(c_61271,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61250,c_61264])).

tff(c_65031,plain,(
    ! [A_2557,B_2558] :
      ( r1_tarski(A_2557,B_2558)
      | ~ m1_subset_1(A_2557,k1_zfmisc_1(B_2558)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_65039,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_61271,c_65031])).

tff(c_58299,plain,(
    ! [A_10] :
      ( A_10 = '#skF_3'
      | ~ r1_tarski(A_10,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58255,c_58255,c_12])).

tff(c_61248,plain,(
    ! [A_10] :
      ( A_10 = '#skF_4'
      | ~ r1_tarski(A_10,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58308,c_58299])).

tff(c_65043,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_65039,c_61248])).

tff(c_58267,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58261,c_74])).

tff(c_61249,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58308,c_58267])).

tff(c_65048,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65043,c_61249])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58256,plain,(
    ! [A_9] : r1_tarski('#skF_2',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58254,c_10])).

tff(c_58273,plain,(
    ! [A_9] : r1_tarski('#skF_3',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58261,c_58256])).

tff(c_61253,plain,(
    ! [A_9] : r1_tarski('#skF_4',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58273])).

tff(c_61305,plain,(
    ! [A_2200,B_2201] :
      ( r1_tarski(A_2200,B_2201)
      | ~ m1_subset_1(A_2200,k1_zfmisc_1(B_2201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61313,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_61271,c_61305])).

tff(c_61317,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_61313,c_61248])).

tff(c_61322,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61317,c_76])).

tff(c_61319,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61317,c_61271])).

tff(c_16,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_58275,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58255,c_58255,c_16])).

tff(c_61251,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58308,c_58275])).

tff(c_61352,plain,(
    ! [C_2207,A_2208,B_2209] :
      ( v1_relat_1(C_2207)
      | ~ m1_subset_1(C_2207,k1_zfmisc_1(k2_zfmisc_1(A_2208,B_2209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_61362,plain,(
    ! [C_2210] :
      ( v1_relat_1(C_2210)
      | ~ m1_subset_1(C_2210,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61251,c_61352])).

tff(c_61370,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_61319,c_61362])).

tff(c_61339,plain,(
    ! [A_2204,B_2205] :
      ( r2_hidden('#skF_1'(A_2204,B_2205),A_2204)
      | r1_tarski(A_2204,B_2205) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61344,plain,(
    ! [A_2204] : r1_tarski(A_2204,A_2204) ),
    inference(resolution,[status(thm)],[c_61339,c_4])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61438,plain,(
    ! [C_2228,A_2229,B_2230] :
      ( v4_relat_1(C_2228,A_2229)
      | ~ m1_subset_1(C_2228,k1_zfmisc_1(k2_zfmisc_1(A_2229,B_2230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_61478,plain,(
    ! [A_2241,A_2242,B_2243] :
      ( v4_relat_1(A_2241,A_2242)
      | ~ r1_tarski(A_2241,k2_zfmisc_1(A_2242,B_2243)) ) ),
    inference(resolution,[status(thm)],[c_22,c_61438])).

tff(c_61493,plain,(
    ! [A_2242,B_2243] : v4_relat_1(k2_zfmisc_1(A_2242,B_2243),A_2242) ),
    inference(resolution,[status(thm)],[c_61344,c_61478])).

tff(c_61505,plain,(
    ! [B_2246,A_2247] :
      ( r1_tarski(k1_relat_1(B_2246),A_2247)
      | ~ v4_relat_1(B_2246,A_2247)
      | ~ v1_relat_1(B_2246) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61537,plain,(
    ! [B_2248] :
      ( k1_relat_1(B_2248) = '#skF_4'
      | ~ v4_relat_1(B_2248,'#skF_4')
      | ~ v1_relat_1(B_2248) ) ),
    inference(resolution,[status(thm)],[c_61505,c_61248])).

tff(c_61541,plain,(
    ! [B_2243] :
      ( k1_relat_1(k2_zfmisc_1('#skF_4',B_2243)) = '#skF_4'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4',B_2243)) ) ),
    inference(resolution,[status(thm)],[c_61493,c_61537])).

tff(c_61552,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61370,c_61250,c_61250,c_61541])).

tff(c_61813,plain,(
    ! [B_2274,A_2275] :
      ( k7_relat_1(B_2274,A_2275) = B_2274
      | ~ r1_tarski(k1_relat_1(B_2274),A_2275)
      | ~ v1_relat_1(B_2274) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_61816,plain,(
    ! [A_2275] :
      ( k7_relat_1('#skF_4',A_2275) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_2275)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61552,c_61813])).

tff(c_61825,plain,(
    ! [A_2275] : k7_relat_1('#skF_4',A_2275) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61370,c_61253,c_61816])).

tff(c_62436,plain,(
    ! [A_2321,B_2322,C_2323,D_2324] :
      ( k2_partfun1(A_2321,B_2322,C_2323,D_2324) = k7_relat_1(C_2323,D_2324)
      | ~ m1_subset_1(C_2323,k1_zfmisc_1(k2_zfmisc_1(A_2321,B_2322)))
      | ~ v1_funct_1(C_2323) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_64969,plain,(
    ! [A_2549,B_2550,A_2551,D_2552] :
      ( k2_partfun1(A_2549,B_2550,A_2551,D_2552) = k7_relat_1(A_2551,D_2552)
      | ~ v1_funct_1(A_2551)
      | ~ r1_tarski(A_2551,k2_zfmisc_1(A_2549,B_2550)) ) ),
    inference(resolution,[status(thm)],[c_22,c_62436])).

tff(c_65003,plain,(
    ! [A_2549,B_2550,D_2552] :
      ( k2_partfun1(A_2549,B_2550,'#skF_4',D_2552) = k7_relat_1('#skF_4',D_2552)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_61253,c_64969])).

tff(c_65015,plain,(
    ! [A_2549,B_2550,D_2552] : k2_partfun1(A_2549,B_2550,'#skF_4',D_2552) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61322,c_61825,c_65003])).

tff(c_58316,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58308,c_58275])).

tff(c_58335,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58308,c_58266])).

tff(c_58336,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58316,c_58335])).

tff(c_58367,plain,(
    ! [A_1915,B_1916] :
      ( r1_tarski(A_1915,B_1916)
      | ~ m1_subset_1(A_1915,k1_zfmisc_1(B_1916)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58371,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58336,c_58367])).

tff(c_58313,plain,(
    ! [A_10] :
      ( A_10 = '#skF_4'
      | ~ r1_tarski(A_10,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58308,c_58299])).

tff(c_58375,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58371,c_58313])).

tff(c_58380,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58375,c_76])).

tff(c_58318,plain,(
    ! [A_9] : r1_tarski('#skF_4',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58273])).

tff(c_59709,plain,(
    ! [A_2059,B_2060,C_2061,D_2062] :
      ( v1_funct_1(k2_partfun1(A_2059,B_2060,C_2061,D_2062))
      | ~ m1_subset_1(C_2061,k1_zfmisc_1(k2_zfmisc_1(A_2059,B_2060)))
      | ~ v1_funct_1(C_2061) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_61208,plain,(
    ! [A_2190,B_2191,A_2192,D_2193] :
      ( v1_funct_1(k2_partfun1(A_2190,B_2191,A_2192,D_2193))
      | ~ v1_funct_1(A_2192)
      | ~ r1_tarski(A_2192,k2_zfmisc_1(A_2190,B_2191)) ) ),
    inference(resolution,[status(thm)],[c_22,c_59709])).

tff(c_61233,plain,(
    ! [A_2190,B_2191,D_2193] :
      ( v1_funct_1(k2_partfun1(A_2190,B_2191,'#skF_4',D_2193))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58318,c_61208])).

tff(c_61242,plain,(
    ! [A_2190,B_2191,D_2193] : v1_funct_1(k2_partfun1(A_2190,B_2191,'#skF_4',D_2193)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58380,c_61233])).

tff(c_58311,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58261,c_58261,c_58275,c_58261,c_66])).

tff(c_58312,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_58311])).

tff(c_58359,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58308,c_58312])).

tff(c_58378,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58375,c_58359])).

tff(c_61245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61242,c_58378])).

tff(c_61246,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_3','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58311])).

tff(c_61302,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58308,c_58308,c_58308,c_58308,c_58308,c_58308,c_61246])).

tff(c_61303,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_61302])).

tff(c_61334,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61317,c_61303])).

tff(c_61338,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_61334])).

tff(c_65020,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65015,c_61338])).

tff(c_65027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61253,c_65020])).

tff(c_65029,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_61302])).

tff(c_65142,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65043,c_65029])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_65150,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_65142,c_20])).

tff(c_65159,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_65150,c_61248])).

tff(c_65028,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_5','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_61302])).

tff(c_65045,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65043,c_65028])).

tff(c_65162,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65159,c_65045])).

tff(c_65169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65048,c_65162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:25:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.19/10.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.19/10.16  
% 19.19/10.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.19/10.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 19.19/10.16  
% 19.19/10.16  %Foreground sorts:
% 19.19/10.16  
% 19.19/10.16  
% 19.19/10.16  %Background operators:
% 19.19/10.16  
% 19.19/10.16  
% 19.19/10.16  %Foreground operators:
% 19.19/10.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.19/10.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.19/10.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.19/10.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 19.19/10.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.19/10.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.19/10.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.19/10.16  tff('#skF_5', type, '#skF_5': $i).
% 19.19/10.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 19.19/10.16  tff('#skF_2', type, '#skF_2': $i).
% 19.19/10.16  tff('#skF_3', type, '#skF_3': $i).
% 19.19/10.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 19.19/10.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 19.19/10.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.19/10.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.19/10.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.19/10.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 19.19/10.16  tff('#skF_4', type, '#skF_4': $i).
% 19.19/10.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.19/10.16  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 19.19/10.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 19.19/10.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.19/10.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.19/10.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.19/10.16  
% 19.19/10.19  tff(f_156, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 19.19/10.19  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 19.19/10.19  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 19.19/10.19  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 19.19/10.19  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 19.19/10.19  tff(f_136, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 19.19/10.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 19.19/10.19  tff(f_130, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 19.19/10.19  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 19.19/10.19  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 19.19/10.19  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 19.19/10.19  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 19.19/10.19  tff(f_104, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 19.19/10.19  tff(f_44, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 19.19/10.19  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 19.19/10.19  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 19.19/10.19  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 19.19/10.19  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 19.19/10.19  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 19.19/10.19  tff(c_70, plain, (r1_tarski('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 19.19/10.19  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 19.19/10.19  tff(c_147, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 19.19/10.19  tff(c_160, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_147])).
% 19.19/10.19  tff(c_68, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_156])).
% 19.19/10.19  tff(c_82, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_68])).
% 19.19/10.19  tff(c_74, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 19.19/10.19  tff(c_56319, plain, (![A_1770, B_1771, C_1772]: (k1_relset_1(A_1770, B_1771, C_1772)=k1_relat_1(C_1772) | ~m1_subset_1(C_1772, k1_zfmisc_1(k2_zfmisc_1(A_1770, B_1771))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.19/10.19  tff(c_56338, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_56319])).
% 19.19/10.19  tff(c_57517, plain, (![B_1881, A_1882, C_1883]: (k1_xboole_0=B_1881 | k1_relset_1(A_1882, B_1881, C_1883)=A_1882 | ~v1_funct_2(C_1883, A_1882, B_1881) | ~m1_subset_1(C_1883, k1_zfmisc_1(k2_zfmisc_1(A_1882, B_1881))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 19.19/10.19  tff(c_57530, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_57517])).
% 19.19/10.19  tff(c_57544, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_56338, c_57530])).
% 19.19/10.19  tff(c_57545, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_57544])).
% 19.19/10.19  tff(c_32, plain, (![B_20, A_19]: (k1_relat_1(k7_relat_1(B_20, A_19))=A_19 | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 19.19/10.19  tff(c_57566, plain, (![A_19]: (k1_relat_1(k7_relat_1('#skF_5', A_19))=A_19 | ~r1_tarski(A_19, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_57545, c_32])).
% 19.19/10.19  tff(c_58163, plain, (![A_1906]: (k1_relat_1(k7_relat_1('#skF_5', A_1906))=A_1906 | ~r1_tarski(A_1906, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_57566])).
% 19.19/10.19  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 19.19/10.19  tff(c_57022, plain, (![A_1843, B_1844, C_1845, D_1846]: (k2_partfun1(A_1843, B_1844, C_1845, D_1846)=k7_relat_1(C_1845, D_1846) | ~m1_subset_1(C_1845, k1_zfmisc_1(k2_zfmisc_1(A_1843, B_1844))) | ~v1_funct_1(C_1845))), inference(cnfTransformation, [status(thm)], [f_136])).
% 19.19/10.19  tff(c_57029, plain, (![D_1846]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_1846)=k7_relat_1('#skF_5', D_1846) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_57022])).
% 19.19/10.19  tff(c_57040, plain, (![D_1846]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_1846)=k7_relat_1('#skF_5', D_1846))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_57029])).
% 19.19/10.19  tff(c_123, plain, (![A_58, B_59]: (r2_hidden('#skF_1'(A_58, B_59), A_58) | r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.19/10.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.19/10.19  tff(c_128, plain, (![A_58]: (r1_tarski(A_58, A_58))), inference(resolution, [status(thm)], [c_123, c_4])).
% 19.19/10.19  tff(c_3235, plain, (![A_339, B_340, C_341]: (k1_relset_1(A_339, B_340, C_341)=k1_relat_1(C_341) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.19/10.19  tff(c_3250, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_3235])).
% 19.19/10.19  tff(c_4665, plain, (![B_468, A_469, C_470]: (k1_xboole_0=B_468 | k1_relset_1(A_469, B_468, C_470)=A_469 | ~v1_funct_2(C_470, A_469, B_468) | ~m1_subset_1(C_470, k1_zfmisc_1(k2_zfmisc_1(A_469, B_468))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 19.19/10.19  tff(c_4675, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_4665])).
% 19.19/10.19  tff(c_4686, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3250, c_4675])).
% 19.19/10.19  tff(c_4687, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_4686])).
% 19.19/10.19  tff(c_4720, plain, (![A_19]: (k1_relat_1(k7_relat_1('#skF_5', A_19))=A_19 | ~r1_tarski(A_19, '#skF_2') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4687, c_32])).
% 19.19/10.19  tff(c_4763, plain, (![A_19]: (k1_relat_1(k7_relat_1('#skF_5', A_19))=A_19 | ~r1_tarski(A_19, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_4720])).
% 19.19/10.19  tff(c_3983, plain, (![A_407, B_408, C_409, D_410]: (k2_partfun1(A_407, B_408, C_409, D_410)=k7_relat_1(C_409, D_410) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(A_407, B_408))) | ~v1_funct_1(C_409))), inference(cnfTransformation, [status(thm)], [f_136])).
% 19.19/10.19  tff(c_3988, plain, (![D_410]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_410)=k7_relat_1('#skF_5', D_410) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_3983])).
% 19.19/10.19  tff(c_3996, plain, (![D_410]: (k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_410)=k7_relat_1('#skF_5', D_410))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3988])).
% 19.19/10.19  tff(c_4831, plain, (![A_473, B_474, C_475, D_476]: (m1_subset_1(k2_partfun1(A_473, B_474, C_475, D_476), k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))) | ~v1_funct_1(C_475))), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.19/10.19  tff(c_4859, plain, (![D_410]: (m1_subset_1(k7_relat_1('#skF_5', D_410), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3996, c_4831])).
% 19.19/10.19  tff(c_5098, plain, (![D_486]: (m1_subset_1(k7_relat_1('#skF_5', D_486), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_4859])).
% 19.19/10.19  tff(c_38, plain, (![C_27, A_25, B_26]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 19.19/10.19  tff(c_5145, plain, (![D_486]: (v1_relat_1(k7_relat_1('#skF_5', D_486)))), inference(resolution, [status(thm)], [c_5098, c_38])).
% 19.19/10.19  tff(c_36, plain, (![B_24, A_23]: (r1_tarski(k2_relat_1(k7_relat_1(B_24, A_23)), k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 19.19/10.19  tff(c_2109, plain, (![B_252, A_253]: (v5_relat_1(B_252, A_253) | ~r1_tarski(k2_relat_1(B_252), A_253) | ~v1_relat_1(B_252))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.19/10.19  tff(c_2117, plain, (![B_24, A_23]: (v5_relat_1(k7_relat_1(B_24, A_23), k2_relat_1(B_24)) | ~v1_relat_1(k7_relat_1(B_24, A_23)) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_36, c_2109])).
% 19.19/10.19  tff(c_2088, plain, (![C_247, B_248, A_249]: (v5_relat_1(C_247, B_248) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 19.19/10.19  tff(c_2103, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_2088])).
% 19.19/10.19  tff(c_30, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.19/10.19  tff(c_2296, plain, (![A_281, C_282, B_283]: (r1_tarski(A_281, C_282) | ~r1_tarski(B_283, C_282) | ~r1_tarski(A_281, B_283))), inference(cnfTransformation, [status(thm)], [f_38])).
% 19.19/10.19  tff(c_9052, plain, (![A_625, A_626, B_627]: (r1_tarski(A_625, A_626) | ~r1_tarski(A_625, k2_relat_1(B_627)) | ~v5_relat_1(B_627, A_626) | ~v1_relat_1(B_627))), inference(resolution, [status(thm)], [c_30, c_2296])).
% 19.19/10.19  tff(c_43642, plain, (![B_1494, A_1495, B_1496]: (r1_tarski(k2_relat_1(B_1494), A_1495) | ~v5_relat_1(B_1496, A_1495) | ~v1_relat_1(B_1496) | ~v5_relat_1(B_1494, k2_relat_1(B_1496)) | ~v1_relat_1(B_1494))), inference(resolution, [status(thm)], [c_30, c_9052])).
% 19.19/10.19  tff(c_43762, plain, (![B_1494]: (r1_tarski(k2_relat_1(B_1494), '#skF_3') | ~v1_relat_1('#skF_5') | ~v5_relat_1(B_1494, k2_relat_1('#skF_5')) | ~v1_relat_1(B_1494))), inference(resolution, [status(thm)], [c_2103, c_43642])).
% 19.19/10.19  tff(c_43893, plain, (![B_1497]: (r1_tarski(k2_relat_1(B_1497), '#skF_3') | ~v5_relat_1(B_1497, k2_relat_1('#skF_5')) | ~v1_relat_1(B_1497))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_43762])).
% 19.19/10.19  tff(c_44023, plain, (![A_23]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_23)), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_5', A_23)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2117, c_43893])).
% 19.19/10.19  tff(c_44136, plain, (![A_23]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_5', A_23)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_5145, c_44023])).
% 19.19/10.19  tff(c_4198, plain, (![C_429, A_430, B_431]: (m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))) | ~r1_tarski(k2_relat_1(C_429), B_431) | ~r1_tarski(k1_relat_1(C_429), A_430) | ~v1_relat_1(C_429))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.19/10.19  tff(c_1995, plain, (![A_227, B_228, C_229, D_230]: (v1_funct_1(k2_partfun1(A_227, B_228, C_229, D_230)) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))) | ~v1_funct_1(C_229))), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.19/10.19  tff(c_2000, plain, (![D_230]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_230)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_1995])).
% 19.19/10.19  tff(c_2008, plain, (![D_230]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', D_230)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2000])).
% 19.19/10.19  tff(c_66, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 19.19/10.19  tff(c_161, plain, (~v1_funct_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 19.19/10.19  tff(c_2011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2008, c_161])).
% 19.19/10.19  tff(c_2012, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 19.19/10.19  tff(c_2020, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2012])).
% 19.19/10.19  tff(c_3999, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3996, c_2020])).
% 19.19/10.19  tff(c_4227, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_4198, c_3999])).
% 19.19/10.19  tff(c_55006, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5145, c_44136, c_4227])).
% 19.19/10.19  tff(c_55021, plain, (~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4763, c_55006])).
% 19.19/10.19  tff(c_55040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_128, c_55021])).
% 19.19/10.19  tff(c_55041, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_2012])).
% 19.19/10.19  tff(c_57048, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_57040, c_55041])).
% 19.19/10.19  tff(c_55042, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_2012])).
% 19.19/10.19  tff(c_57047, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_57040, c_55042])).
% 19.19/10.19  tff(c_44, plain, (![A_31, B_32, C_33]: (k1_relset_1(A_31, B_32, C_33)=k1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.19/10.19  tff(c_57133, plain, (k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_57047, c_44])).
% 19.19/10.19  tff(c_57261, plain, (![B_1856, C_1857, A_1858]: (k1_xboole_0=B_1856 | v1_funct_2(C_1857, A_1858, B_1856) | k1_relset_1(A_1858, B_1856, C_1857)!=A_1858 | ~m1_subset_1(C_1857, k1_zfmisc_1(k2_zfmisc_1(A_1858, B_1856))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 19.19/10.19  tff(c_57267, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_57047, c_57261])).
% 19.19/10.19  tff(c_57283, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_4'), '#skF_4', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57133, c_57267])).
% 19.19/10.19  tff(c_57284, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_57048, c_82, c_57283])).
% 19.19/10.19  tff(c_58172, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58163, c_57284])).
% 19.19/10.19  tff(c_58253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_58172])).
% 19.19/10.19  tff(c_58255, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_68])).
% 19.19/10.19  tff(c_58254, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_68])).
% 19.19/10.19  tff(c_58261, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58255, c_58254])).
% 19.19/10.19  tff(c_58268, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58261, c_70])).
% 19.19/10.19  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 19.19/10.19  tff(c_58300, plain, (![A_1910]: (A_1910='#skF_3' | ~r1_tarski(A_1910, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58255, c_58255, c_12])).
% 19.19/10.19  tff(c_58308, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_58268, c_58300])).
% 19.19/10.19  tff(c_18, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 19.19/10.19  tff(c_58283, plain, (![B_12]: (k2_zfmisc_1('#skF_3', B_12)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58255, c_58255, c_18])).
% 19.19/10.19  tff(c_61250, plain, (![B_12]: (k2_zfmisc_1('#skF_4', B_12)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58308, c_58283])).
% 19.19/10.19  tff(c_58266, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58261, c_72])).
% 19.19/10.19  tff(c_61264, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58308, c_58266])).
% 19.19/10.19  tff(c_61271, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_61250, c_61264])).
% 19.19/10.19  tff(c_65031, plain, (![A_2557, B_2558]: (r1_tarski(A_2557, B_2558) | ~m1_subset_1(A_2557, k1_zfmisc_1(B_2558)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.19/10.19  tff(c_65039, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_61271, c_65031])).
% 19.19/10.19  tff(c_58299, plain, (![A_10]: (A_10='#skF_3' | ~r1_tarski(A_10, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58255, c_58255, c_12])).
% 19.19/10.19  tff(c_61248, plain, (![A_10]: (A_10='#skF_4' | ~r1_tarski(A_10, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58308, c_58299])).
% 19.19/10.19  tff(c_65043, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_65039, c_61248])).
% 19.19/10.19  tff(c_58267, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58261, c_74])).
% 19.19/10.19  tff(c_61249, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58308, c_58267])).
% 19.19/10.19  tff(c_65048, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65043, c_61249])).
% 19.19/10.19  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 19.19/10.19  tff(c_58256, plain, (![A_9]: (r1_tarski('#skF_2', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_58254, c_10])).
% 19.19/10.19  tff(c_58273, plain, (![A_9]: (r1_tarski('#skF_3', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_58261, c_58256])).
% 19.19/10.19  tff(c_61253, plain, (![A_9]: (r1_tarski('#skF_4', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58273])).
% 19.19/10.19  tff(c_61305, plain, (![A_2200, B_2201]: (r1_tarski(A_2200, B_2201) | ~m1_subset_1(A_2200, k1_zfmisc_1(B_2201)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.19/10.19  tff(c_61313, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_61271, c_61305])).
% 19.19/10.19  tff(c_61317, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_61313, c_61248])).
% 19.19/10.19  tff(c_61322, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61317, c_76])).
% 19.19/10.19  tff(c_61319, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_61317, c_61271])).
% 19.19/10.19  tff(c_16, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 19.19/10.19  tff(c_58275, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58255, c_58255, c_16])).
% 19.19/10.19  tff(c_61251, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58308, c_58275])).
% 19.19/10.19  tff(c_61352, plain, (![C_2207, A_2208, B_2209]: (v1_relat_1(C_2207) | ~m1_subset_1(C_2207, k1_zfmisc_1(k2_zfmisc_1(A_2208, B_2209))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 19.19/10.19  tff(c_61362, plain, (![C_2210]: (v1_relat_1(C_2210) | ~m1_subset_1(C_2210, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_61251, c_61352])).
% 19.19/10.19  tff(c_61370, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_61319, c_61362])).
% 19.19/10.19  tff(c_61339, plain, (![A_2204, B_2205]: (r2_hidden('#skF_1'(A_2204, B_2205), A_2204) | r1_tarski(A_2204, B_2205))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.19/10.19  tff(c_61344, plain, (![A_2204]: (r1_tarski(A_2204, A_2204))), inference(resolution, [status(thm)], [c_61339, c_4])).
% 19.19/10.19  tff(c_22, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.19/10.19  tff(c_61438, plain, (![C_2228, A_2229, B_2230]: (v4_relat_1(C_2228, A_2229) | ~m1_subset_1(C_2228, k1_zfmisc_1(k2_zfmisc_1(A_2229, B_2230))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 19.19/10.19  tff(c_61478, plain, (![A_2241, A_2242, B_2243]: (v4_relat_1(A_2241, A_2242) | ~r1_tarski(A_2241, k2_zfmisc_1(A_2242, B_2243)))), inference(resolution, [status(thm)], [c_22, c_61438])).
% 19.19/10.19  tff(c_61493, plain, (![A_2242, B_2243]: (v4_relat_1(k2_zfmisc_1(A_2242, B_2243), A_2242))), inference(resolution, [status(thm)], [c_61344, c_61478])).
% 19.19/10.19  tff(c_61505, plain, (![B_2246, A_2247]: (r1_tarski(k1_relat_1(B_2246), A_2247) | ~v4_relat_1(B_2246, A_2247) | ~v1_relat_1(B_2246))), inference(cnfTransformation, [status(thm)], [f_60])).
% 19.19/10.19  tff(c_61537, plain, (![B_2248]: (k1_relat_1(B_2248)='#skF_4' | ~v4_relat_1(B_2248, '#skF_4') | ~v1_relat_1(B_2248))), inference(resolution, [status(thm)], [c_61505, c_61248])).
% 19.19/10.19  tff(c_61541, plain, (![B_2243]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_2243))='#skF_4' | ~v1_relat_1(k2_zfmisc_1('#skF_4', B_2243)))), inference(resolution, [status(thm)], [c_61493, c_61537])).
% 19.19/10.19  tff(c_61552, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_61370, c_61250, c_61250, c_61541])).
% 19.19/10.19  tff(c_61813, plain, (![B_2274, A_2275]: (k7_relat_1(B_2274, A_2275)=B_2274 | ~r1_tarski(k1_relat_1(B_2274), A_2275) | ~v1_relat_1(B_2274))), inference(cnfTransformation, [status(thm)], [f_78])).
% 19.19/10.19  tff(c_61816, plain, (![A_2275]: (k7_relat_1('#skF_4', A_2275)='#skF_4' | ~r1_tarski('#skF_4', A_2275) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_61552, c_61813])).
% 19.19/10.19  tff(c_61825, plain, (![A_2275]: (k7_relat_1('#skF_4', A_2275)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61370, c_61253, c_61816])).
% 19.19/10.19  tff(c_62436, plain, (![A_2321, B_2322, C_2323, D_2324]: (k2_partfun1(A_2321, B_2322, C_2323, D_2324)=k7_relat_1(C_2323, D_2324) | ~m1_subset_1(C_2323, k1_zfmisc_1(k2_zfmisc_1(A_2321, B_2322))) | ~v1_funct_1(C_2323))), inference(cnfTransformation, [status(thm)], [f_136])).
% 19.19/10.19  tff(c_64969, plain, (![A_2549, B_2550, A_2551, D_2552]: (k2_partfun1(A_2549, B_2550, A_2551, D_2552)=k7_relat_1(A_2551, D_2552) | ~v1_funct_1(A_2551) | ~r1_tarski(A_2551, k2_zfmisc_1(A_2549, B_2550)))), inference(resolution, [status(thm)], [c_22, c_62436])).
% 19.19/10.19  tff(c_65003, plain, (![A_2549, B_2550, D_2552]: (k2_partfun1(A_2549, B_2550, '#skF_4', D_2552)=k7_relat_1('#skF_4', D_2552) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_61253, c_64969])).
% 19.19/10.19  tff(c_65015, plain, (![A_2549, B_2550, D_2552]: (k2_partfun1(A_2549, B_2550, '#skF_4', D_2552)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61322, c_61825, c_65003])).
% 19.19/10.19  tff(c_58316, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58308, c_58275])).
% 19.19/10.19  tff(c_58335, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58308, c_58266])).
% 19.19/10.19  tff(c_58336, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58316, c_58335])).
% 19.19/10.19  tff(c_58367, plain, (![A_1915, B_1916]: (r1_tarski(A_1915, B_1916) | ~m1_subset_1(A_1915, k1_zfmisc_1(B_1916)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.19/10.19  tff(c_58371, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58336, c_58367])).
% 19.19/10.19  tff(c_58313, plain, (![A_10]: (A_10='#skF_4' | ~r1_tarski(A_10, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58308, c_58299])).
% 19.19/10.19  tff(c_58375, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_58371, c_58313])).
% 19.19/10.19  tff(c_58380, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58375, c_76])).
% 19.19/10.19  tff(c_58318, plain, (![A_9]: (r1_tarski('#skF_4', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58273])).
% 19.19/10.19  tff(c_59709, plain, (![A_2059, B_2060, C_2061, D_2062]: (v1_funct_1(k2_partfun1(A_2059, B_2060, C_2061, D_2062)) | ~m1_subset_1(C_2061, k1_zfmisc_1(k2_zfmisc_1(A_2059, B_2060))) | ~v1_funct_1(C_2061))), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.19/10.19  tff(c_61208, plain, (![A_2190, B_2191, A_2192, D_2193]: (v1_funct_1(k2_partfun1(A_2190, B_2191, A_2192, D_2193)) | ~v1_funct_1(A_2192) | ~r1_tarski(A_2192, k2_zfmisc_1(A_2190, B_2191)))), inference(resolution, [status(thm)], [c_22, c_59709])).
% 19.19/10.19  tff(c_61233, plain, (![A_2190, B_2191, D_2193]: (v1_funct_1(k2_partfun1(A_2190, B_2191, '#skF_4', D_2193)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58318, c_61208])).
% 19.19/10.19  tff(c_61242, plain, (![A_2190, B_2191, D_2193]: (v1_funct_1(k2_partfun1(A_2190, B_2191, '#skF_4', D_2193)))), inference(demodulation, [status(thm), theory('equality')], [c_58380, c_61233])).
% 19.19/10.19  tff(c_58311, plain, (~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3')) | ~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58261, c_58261, c_58275, c_58261, c_66])).
% 19.19/10.19  tff(c_58312, plain, (~v1_funct_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_58311])).
% 19.19/10.19  tff(c_58359, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58308, c_58312])).
% 19.19/10.19  tff(c_58378, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58375, c_58359])).
% 19.19/10.19  tff(c_61245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61242, c_58378])).
% 19.19/10.19  tff(c_61246, plain, (~v1_funct_2(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_3', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_58311])).
% 19.19/10.19  tff(c_61302, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58308, c_58308, c_58308, c_58308, c_58308, c_58308, c_61246])).
% 19.19/10.19  tff(c_61303, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_61302])).
% 19.19/10.19  tff(c_61334, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_61317, c_61303])).
% 19.19/10.19  tff(c_61338, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_22, c_61334])).
% 19.19/10.19  tff(c_65020, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65015, c_61338])).
% 19.19/10.19  tff(c_65027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61253, c_65020])).
% 19.19/10.19  tff(c_65029, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_61302])).
% 19.19/10.19  tff(c_65142, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_65043, c_65029])).
% 19.19/10.19  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.19/10.19  tff(c_65150, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_65142, c_20])).
% 19.19/10.19  tff(c_65159, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_65150, c_61248])).
% 19.19/10.19  tff(c_65028, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_5', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_61302])).
% 19.19/10.19  tff(c_65045, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65043, c_65028])).
% 19.19/10.19  tff(c_65162, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65159, c_65045])).
% 19.19/10.19  tff(c_65169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65048, c_65162])).
% 19.19/10.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.19/10.19  
% 19.19/10.19  Inference rules
% 19.19/10.19  ----------------------
% 19.19/10.19  #Ref     : 0
% 19.19/10.19  #Sup     : 13868
% 19.19/10.19  #Fact    : 0
% 19.19/10.19  #Define  : 0
% 19.19/10.19  #Split   : 54
% 19.19/10.19  #Chain   : 0
% 19.19/10.19  #Close   : 0
% 19.19/10.19  
% 19.19/10.19  Ordering : KBO
% 19.19/10.19  
% 19.19/10.19  Simplification rules
% 19.19/10.19  ----------------------
% 19.19/10.19  #Subsume      : 3961
% 19.19/10.19  #Demod        : 14609
% 19.19/10.19  #Tautology    : 4004
% 19.19/10.19  #SimpNegUnit  : 139
% 19.19/10.19  #BackRed      : 102
% 19.19/10.19  
% 19.19/10.19  #Partial instantiations: 0
% 19.19/10.19  #Strategies tried      : 1
% 19.19/10.19  
% 19.19/10.19  Timing (in seconds)
% 19.19/10.19  ----------------------
% 19.19/10.19  Preprocessing        : 0.38
% 19.19/10.19  Parsing              : 0.20
% 19.19/10.19  CNF conversion       : 0.03
% 19.19/10.19  Main loop            : 9.02
% 19.19/10.19  Inferencing          : 1.84
% 19.19/10.19  Reduction            : 3.66
% 19.19/10.19  Demodulation         : 2.79
% 19.19/10.19  BG Simplification    : 0.16
% 19.19/10.19  Subsumption          : 2.77
% 19.19/10.19  Abstraction          : 0.26
% 19.19/10.19  MUC search           : 0.00
% 19.19/10.19  Cooper               : 0.00
% 19.19/10.19  Total                : 9.46
% 19.19/10.19  Index Insertion      : 0.00
% 19.19/10.19  Index Deletion       : 0.00
% 19.19/10.19  Index Matching       : 0.00
% 19.19/10.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
