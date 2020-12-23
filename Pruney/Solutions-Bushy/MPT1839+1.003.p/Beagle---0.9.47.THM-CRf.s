%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1839+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:30 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 228 expanded)
%              Number of leaves         :   30 (  89 expanded)
%              Depth                    :   21
%              Number of atoms          :  175 ( 552 expanded)
%              Number of equality atoms :   27 (  87 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(c_46,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61,plain,(
    ! [B_37,A_38] : r1_tarski(k3_xboole_0(B_37,A_38),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_18])).

tff(c_12,plain,(
    ! [A_7] :
      ( v1_xboole_0(A_7)
      | r2_hidden('#skF_2'(A_7),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_147,plain,(
    ! [C_59,B_60,A_61] :
      ( ~ v1_xboole_0(C_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(C_59))
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_171,plain,(
    ! [B_65,A_66,A_67] :
      ( ~ v1_xboole_0(B_65)
      | ~ r2_hidden(A_66,A_67)
      | ~ r1_tarski(A_67,B_65) ) ),
    inference(resolution,[status(thm)],[c_30,c_147])).

tff(c_187,plain,(
    ! [B_69,A_70] :
      ( ~ v1_xboole_0(B_69)
      | ~ r1_tarski(A_70,B_69)
      | v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_12,c_171])).

tff(c_204,plain,(
    ! [A_71,B_72] :
      ( ~ v1_xboole_0(A_71)
      | v1_xboole_0(k3_xboole_0(B_72,A_71)) ) ),
    inference(resolution,[status(thm)],[c_61,c_187])).

tff(c_38,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_214,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_204,c_38])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    ! [A_11] : m1_subset_1('#skF_3'(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_259,plain,(
    ! [A_80,C_81,B_82] :
      ( m1_subset_1(A_80,C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_283,plain,(
    ! [A_86,B_87,A_88] :
      ( m1_subset_1(A_86,B_87)
      | ~ r2_hidden(A_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(resolution,[status(thm)],[c_30,c_259])).

tff(c_388,plain,(
    ! [A_101,B_102,B_103] :
      ( m1_subset_1(A_101,B_102)
      | ~ r1_tarski(B_103,B_102)
      | v1_xboole_0(B_103)
      | ~ m1_subset_1(A_101,B_103) ) ),
    inference(resolution,[status(thm)],[c_22,c_283])).

tff(c_759,plain,(
    ! [A_130,A_131,B_132] :
      ( m1_subset_1(A_130,A_131)
      | v1_xboole_0(k3_xboole_0(A_131,B_132))
      | ~ m1_subset_1(A_130,k3_xboole_0(A_131,B_132)) ) ),
    inference(resolution,[status(thm)],[c_18,c_388])).

tff(c_800,plain,(
    ! [A_131,B_132] :
      ( m1_subset_1('#skF_3'(k3_xboole_0(A_131,B_132)),A_131)
      | v1_xboole_0(k3_xboole_0(A_131,B_132)) ) ),
    inference(resolution,[status(thm)],[c_14,c_759])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_1'(A_3),A_3)
      | ~ v1_zfmisc_1(A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_215,plain,(
    ! [A_73,B_74] :
      ( k6_domain_1(A_73,B_74) = k1_tarski(B_74)
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_373,plain,(
    ! [A_100] :
      ( k6_domain_1(A_100,'#skF_1'(A_100)) = k1_tarski('#skF_1'(A_100))
      | ~ v1_zfmisc_1(A_100)
      | v1_xboole_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_8,c_215])).

tff(c_6,plain,(
    ! [A_3] :
      ( k6_domain_1(A_3,'#skF_1'(A_3)) = A_3
      | ~ v1_zfmisc_1(A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_485,plain,(
    ! [A_108] :
      ( k1_tarski('#skF_1'(A_108)) = A_108
      | ~ v1_zfmisc_1(A_108)
      | v1_xboole_0(A_108)
      | ~ v1_zfmisc_1(A_108)
      | v1_xboole_0(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_6])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_tarski(A_21),B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_117,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(k1_tarski(A_51),k1_tarski(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_122,plain,(
    ! [B_50,A_21] :
      ( B_50 = A_21
      | ~ r2_hidden(A_21,k1_tarski(B_50)) ) ),
    inference(resolution,[status(thm)],[c_26,c_117])).

tff(c_1650,plain,(
    ! [A_204,A_205] :
      ( A_204 = '#skF_1'(A_205)
      | ~ r2_hidden(A_204,A_205)
      | ~ v1_zfmisc_1(A_205)
      | v1_xboole_0(A_205)
      | ~ v1_zfmisc_1(A_205)
      | v1_xboole_0(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_122])).

tff(c_1805,plain,(
    ! [A_212,B_213] :
      ( A_212 = '#skF_1'(B_213)
      | ~ v1_zfmisc_1(B_213)
      | v1_xboole_0(B_213)
      | ~ m1_subset_1(A_212,B_213) ) ),
    inference(resolution,[status(thm)],[c_22,c_1650])).

tff(c_1863,plain,(
    ! [A_214] :
      ( '#skF_1'(A_214) = '#skF_3'(A_214)
      | ~ v1_zfmisc_1(A_214)
      | v1_xboole_0(A_214) ) ),
    inference(resolution,[status(thm)],[c_14,c_1805])).

tff(c_1866,plain,
    ( '#skF_1'('#skF_4') = '#skF_3'('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1863])).

tff(c_1869,plain,(
    '#skF_1'('#skF_4') = '#skF_3'('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1866])).

tff(c_379,plain,(
    ! [A_100] :
      ( k1_tarski('#skF_1'(A_100)) = A_100
      | ~ v1_zfmisc_1(A_100)
      | v1_xboole_0(A_100)
      | ~ v1_zfmisc_1(A_100)
      | v1_xboole_0(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_6])).

tff(c_1877,plain,
    ( k1_tarski('#skF_3'('#skF_4')) = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1869,c_379])).

tff(c_1890,plain,
    ( k1_tarski('#skF_3'('#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_1877])).

tff(c_1891,plain,(
    k1_tarski('#skF_3'('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1890])).

tff(c_137,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | v1_xboole_0(B_58)
      | ~ m1_subset_1(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,(
    ! [B_50,A_57] :
      ( B_50 = A_57
      | v1_xboole_0(k1_tarski(B_50))
      | ~ m1_subset_1(A_57,k1_tarski(B_50)) ) ),
    inference(resolution,[status(thm)],[c_137,c_122])).

tff(c_1977,plain,(
    ! [A_57] :
      ( A_57 = '#skF_3'('#skF_4')
      | v1_xboole_0(k1_tarski('#skF_3'('#skF_4')))
      | ~ m1_subset_1(A_57,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1891,c_145])).

tff(c_2016,plain,(
    ! [A_57] :
      ( A_57 = '#skF_3'('#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_57,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1891,c_1977])).

tff(c_2041,plain,(
    ! [A_215] :
      ( A_215 = '#skF_3'('#skF_4')
      | ~ m1_subset_1(A_215,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2016])).

tff(c_2911,plain,(
    ! [B_248] :
      ( '#skF_3'(k3_xboole_0('#skF_4',B_248)) = '#skF_3'('#skF_4')
      | v1_xboole_0(k3_xboole_0('#skF_4',B_248)) ) ),
    inference(resolution,[status(thm)],[c_800,c_2041])).

tff(c_2923,plain,(
    '#skF_3'(k3_xboole_0('#skF_4','#skF_5')) = '#skF_3'('#skF_4') ),
    inference(resolution,[status(thm)],[c_2911,c_38])).

tff(c_801,plain,(
    ! [A_133,B_134] :
      ( m1_subset_1('#skF_3'(k3_xboole_0(A_133,B_134)),A_133)
      | v1_xboole_0(k3_xboole_0(A_133,B_134)) ) ),
    inference(resolution,[status(thm)],[c_14,c_759])).

tff(c_836,plain,(
    ! [B_2,A_1] :
      ( m1_subset_1('#skF_3'(k3_xboole_0(B_2,A_1)),A_1)
      | v1_xboole_0(k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_801])).

tff(c_2927,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),'#skF_5')
    | v1_xboole_0(k3_xboole_0('#skF_5','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2923,c_836])).

tff(c_2951,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),'#skF_5')
    | v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2927])).

tff(c_2952,plain,(
    m1_subset_1('#skF_3'('#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2951])).

tff(c_2106,plain,(
    ! [A_216,B_217] :
      ( r1_tarski(A_216,B_217)
      | ~ r2_hidden('#skF_1'(A_216),B_217)
      | ~ v1_zfmisc_1(A_216)
      | v1_xboole_0(A_216)
      | ~ v1_zfmisc_1(A_216)
      | v1_xboole_0(A_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_26])).

tff(c_2109,plain,(
    ! [B_217] :
      ( r1_tarski('#skF_4',B_217)
      | ~ r2_hidden('#skF_3'('#skF_4'),B_217)
      | ~ v1_zfmisc_1('#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ v1_zfmisc_1('#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1869,c_2106])).

tff(c_2115,plain,(
    ! [B_217] :
      ( r1_tarski('#skF_4',B_217)
      | ~ r2_hidden('#skF_3'('#skF_4'),B_217)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_2109])).

tff(c_2210,plain,(
    ! [B_220] :
      ( r1_tarski('#skF_4',B_220)
      | ~ r2_hidden('#skF_3'('#skF_4'),B_220) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2115])).

tff(c_2219,plain,(
    ! [B_20] :
      ( r1_tarski('#skF_4',B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1('#skF_3'('#skF_4'),B_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_2210])).

tff(c_2966,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2952,c_2219])).

tff(c_2979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_36,c_2966])).

%------------------------------------------------------------------------------
