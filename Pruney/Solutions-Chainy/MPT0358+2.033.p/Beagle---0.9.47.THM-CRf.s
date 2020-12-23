%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:04 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 335 expanded)
%              Number of leaves         :   39 ( 127 expanded)
%              Depth                    :   23
%              Number of atoms          :  195 ( 584 expanded)
%              Number of equality atoms :   78 ( 216 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_118,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_115,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_111,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_76,plain,(
    ! [A_42] : ~ v1_xboole_0(k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_199,plain,(
    ! [B_77,A_78] :
      ( r2_hidden(B_77,A_78)
      | ~ m1_subset_1(B_77,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_52,plain,(
    ! [C_36,A_32] :
      ( r1_tarski(C_36,A_32)
      | ~ r2_hidden(C_36,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_207,plain,(
    ! [B_77,A_32] :
      ( r1_tarski(B_77,A_32)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_32))
      | v1_xboole_0(k1_zfmisc_1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_199,c_52])).

tff(c_241,plain,(
    ! [B_82,A_83] :
      ( r1_tarski(B_82,A_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_207])).

tff(c_250,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_241])).

tff(c_38,plain,(
    ! [B_20] : r1_tarski(B_20,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_54,plain,(
    ! [C_36,A_32] :
      ( r2_hidden(C_36,k1_zfmisc_1(A_32))
      | ~ r1_tarski(C_36,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_349,plain,(
    ! [B_91,A_92] :
      ( m1_subset_1(B_91,A_92)
      | ~ r2_hidden(B_91,A_92)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_367,plain,(
    ! [C_36,A_32] :
      ( m1_subset_1(C_36,k1_zfmisc_1(A_32))
      | v1_xboole_0(k1_zfmisc_1(A_32))
      | ~ r1_tarski(C_36,A_32) ) ),
    inference(resolution,[status(thm)],[c_54,c_349])).

tff(c_375,plain,(
    ! [C_36,A_32] :
      ( m1_subset_1(C_36,k1_zfmisc_1(A_32))
      | ~ r1_tarski(C_36,A_32) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_367])).

tff(c_580,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(A_115,B_116) = k3_subset_1(A_115,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_659,plain,(
    ! [A_119,C_120] :
      ( k4_xboole_0(A_119,C_120) = k3_subset_1(A_119,C_120)
      | ~ r1_tarski(C_120,A_119) ) ),
    inference(resolution,[status(thm)],[c_375,c_580])).

tff(c_672,plain,(
    ! [B_20] : k4_xboole_0(B_20,B_20) = k3_subset_1(B_20,B_20) ),
    inference(resolution,[status(thm)],[c_38,c_659])).

tff(c_109,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = A_55
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_113,plain,(
    ! [B_20] : k3_xboole_0(B_20,B_20) = B_20 ),
    inference(resolution,[status(thm)],[c_38,c_109])).

tff(c_675,plain,(
    ! [B_121] : k4_xboole_0(B_121,B_121) = k3_subset_1(B_121,B_121) ),
    inference(resolution,[status(thm)],[c_38,c_659])).

tff(c_44,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_692,plain,(
    ! [B_121] : k4_xboole_0(B_121,k3_subset_1(B_121,B_121)) = k3_xboole_0(B_121,B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_44])).

tff(c_720,plain,(
    ! [B_123] : k4_xboole_0(B_123,k3_subset_1(B_123,B_123)) = B_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_692])).

tff(c_729,plain,(
    ! [B_123] : k3_xboole_0(B_123,k3_subset_1(B_123,B_123)) = k4_xboole_0(B_123,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_44])).

tff(c_737,plain,(
    ! [B_123] : k3_xboole_0(B_123,k3_subset_1(B_123,B_123)) = k3_subset_1(B_123,B_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_729])).

tff(c_708,plain,(
    ! [B_121] : k4_xboole_0(B_121,k3_subset_1(B_121,B_121)) = B_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_692])).

tff(c_414,plain,(
    ! [A_96,B_97] : k4_xboole_0(A_96,k4_xboole_0(A_96,B_97)) = k3_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_417,plain,(
    ! [A_96,B_97] : k4_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k3_xboole_0(A_96,k4_xboole_0(A_96,B_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_44])).

tff(c_72,plain,(
    ! [A_39] : k1_subset_1(A_39) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_80,plain,
    ( k1_subset_1('#skF_8') != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_88,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_80])).

tff(c_108,plain,(
    ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_86,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_subset_1('#skF_8') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_87,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_86])).

tff(c_123,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_87])).

tff(c_32,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_5'(A_17),A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_124,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_5'(A_17),A_17)
      | A_17 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_32])).

tff(c_293,plain,(
    ! [D_85,A_86,B_87] :
      ( r2_hidden(D_85,A_86)
      | ~ r2_hidden(D_85,k3_xboole_0(A_86,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_324,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_86,B_87)),A_86)
      | k3_xboole_0(A_86,B_87) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_124,c_293])).

tff(c_48,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k4_xboole_0(A_27,B_28) != A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_456,plain,(
    ! [A_100,B_101,C_102] :
      ( ~ r1_xboole_0(A_100,B_101)
      | ~ r2_hidden(C_102,B_101)
      | ~ r2_hidden(C_102,A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1307,plain,(
    ! [C_166,B_167,A_168] :
      ( ~ r2_hidden(C_166,B_167)
      | ~ r2_hidden(C_166,A_168)
      | k4_xboole_0(A_168,B_167) != A_168 ) ),
    inference(resolution,[status(thm)],[c_48,c_456])).

tff(c_1662,plain,(
    ! [A_191,A_192] :
      ( ~ r2_hidden('#skF_5'(A_191),A_192)
      | k4_xboole_0(A_192,A_191) != A_192
      | A_191 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_124,c_1307])).

tff(c_1665,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,k3_xboole_0(A_86,B_87)) != A_86
      | k3_xboole_0(A_86,B_87) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_324,c_1662])).

tff(c_1797,plain,(
    ! [A_200,B_201] :
      ( k3_xboole_0(A_200,k4_xboole_0(A_200,B_201)) != A_200
      | k3_xboole_0(A_200,B_201) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_1665])).

tff(c_1818,plain,(
    ! [B_121] :
      ( k3_xboole_0(B_121,B_121) != B_121
      | k3_xboole_0(B_121,k3_subset_1(B_121,B_121)) = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_1797])).

tff(c_1845,plain,(
    ! [B_121] : k3_subset_1(B_121,B_121) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_113,c_1818])).

tff(c_1865,plain,(
    ! [B_121] : k4_xboole_0(B_121,'#skF_9') = B_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_708])).

tff(c_600,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_580])).

tff(c_1948,plain,(
    k3_subset_1('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1865,c_600])).

tff(c_2103,plain,(
    ~ r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_108])).

tff(c_2106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_2103])).

tff(c_2107,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_2210,plain,(
    ! [B_232,A_233] :
      ( r2_hidden(B_232,A_233)
      | ~ m1_subset_1(B_232,A_233)
      | v1_xboole_0(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2214,plain,(
    ! [B_232,A_32] :
      ( r1_tarski(B_232,A_32)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(A_32))
      | v1_xboole_0(k1_zfmisc_1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_2210,c_52])).

tff(c_2245,plain,(
    ! [B_236,A_237] :
      ( r1_tarski(B_236,A_237)
      | ~ m1_subset_1(B_236,k1_zfmisc_1(A_237)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2214])).

tff(c_2254,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_2245])).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2261,plain,(
    k3_xboole_0('#skF_9','#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2254,c_42])).

tff(c_2371,plain,(
    ! [D_247,B_248,A_249] :
      ( r2_hidden(D_247,B_248)
      | ~ r2_hidden(D_247,k3_xboole_0(A_249,B_248)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2406,plain,(
    ! [D_250] :
      ( r2_hidden(D_250,'#skF_8')
      | ~ r2_hidden(D_250,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2261,c_2371])).

tff(c_2426,plain,
    ( r2_hidden('#skF_5'('#skF_9'),'#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_32,c_2406])).

tff(c_2433,plain,(
    r2_hidden('#skF_5'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2107,c_2426])).

tff(c_8,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,k3_xboole_0(A_6,B_7))
      | ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2130,plain,(
    ! [A_215,B_216] :
      ( k3_xboole_0(A_215,B_216) = A_215
      | ~ r1_tarski(A_215,B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2138,plain,(
    ! [B_20] : k3_xboole_0(B_20,B_20) = B_20 ),
    inference(resolution,[status(thm)],[c_38,c_2130])).

tff(c_2731,plain,(
    ! [A_278,B_279] :
      ( k4_xboole_0(A_278,B_279) = k3_subset_1(A_278,B_279)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(A_278)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2758,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_2731])).

tff(c_2158,plain,(
    ! [A_220,C_221,B_222] :
      ( r1_xboole_0(A_220,k4_xboole_0(C_221,B_222))
      | ~ r1_tarski(A_220,B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = A_27
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2162,plain,(
    ! [A_220,C_221,B_222] :
      ( k4_xboole_0(A_220,k4_xboole_0(C_221,B_222)) = A_220
      | ~ r1_tarski(A_220,B_222) ) ),
    inference(resolution,[status(thm)],[c_2158,c_46])).

tff(c_2793,plain,(
    ! [A_281] :
      ( k4_xboole_0(A_281,k3_subset_1('#skF_8','#skF_9')) = A_281
      | ~ r1_tarski(A_281,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2758,c_2162])).

tff(c_40,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2265,plain,(
    k5_xboole_0('#skF_9','#skF_9') = k4_xboole_0('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2261,c_40])).

tff(c_2186,plain,(
    ! [A_229,B_230] : k5_xboole_0(A_229,k3_xboole_0(A_229,B_230)) = k4_xboole_0(A_229,B_230) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2198,plain,(
    ! [B_20] : k5_xboole_0(B_20,B_20) = k4_xboole_0(B_20,B_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_2186])).

tff(c_2273,plain,(
    k4_xboole_0('#skF_9','#skF_9') = k4_xboole_0('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2265,c_2198])).

tff(c_2108,plain,(
    r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_2137,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2108,c_2130])).

tff(c_2195,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k5_xboole_0('#skF_9','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2137,c_2186])).

tff(c_2476,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = k4_xboole_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2273,c_2198,c_2195])).

tff(c_2805,plain,
    ( k4_xboole_0('#skF_9','#skF_8') = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2793,c_2476])).

tff(c_2823,plain,(
    k4_xboole_0('#skF_9','#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2805])).

tff(c_2963,plain,(
    ! [A_288] :
      ( k4_xboole_0(A_288,'#skF_9') = A_288
      | ~ r1_tarski(A_288,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2823,c_2162])).

tff(c_2983,plain,(
    k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_38,c_2963])).

tff(c_2984,plain,(
    k3_subset_1('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2983,c_2758])).

tff(c_2765,plain,(
    k4_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2758,c_44])).

tff(c_3022,plain,(
    k4_xboole_0('#skF_8','#skF_8') = k3_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2984,c_2765])).

tff(c_3048,plain,(
    k4_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_9')) = k3_xboole_0('#skF_8','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3022,c_44])).

tff(c_3054,plain,(
    k4_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2138,c_3048])).

tff(c_50,plain,(
    ! [A_29,C_31,B_30] :
      ( r1_xboole_0(A_29,k4_xboole_0(C_31,B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3121,plain,(
    ! [A_296] :
      ( r1_xboole_0(A_296,'#skF_8')
      | ~ r1_tarski(A_296,k3_xboole_0('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3054,c_50])).

tff(c_3141,plain,(
    r1_xboole_0(k3_xboole_0('#skF_8','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_3121])).

tff(c_26,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,B_13)
      | ~ r2_hidden(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3171,plain,(
    ! [C_297] :
      ( ~ r2_hidden(C_297,'#skF_8')
      | ~ r2_hidden(C_297,k3_xboole_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_3141,c_26])).

tff(c_3265,plain,(
    ! [D_300] :
      ( ~ r2_hidden(D_300,'#skF_9')
      | ~ r2_hidden(D_300,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8,c_3171])).

tff(c_3297,plain,
    ( ~ r2_hidden('#skF_5'('#skF_9'),'#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_32,c_3265])).

tff(c_3310,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2433,c_3297])).

tff(c_3312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2107,c_3310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:30:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.84  
% 4.64/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_4
% 4.64/1.84  
% 4.64/1.84  %Foreground sorts:
% 4.64/1.84  
% 4.64/1.84  
% 4.64/1.84  %Background operators:
% 4.64/1.84  
% 4.64/1.84  
% 4.64/1.84  %Foreground operators:
% 4.64/1.84  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.64/1.84  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.64/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.64/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.64/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.64/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.64/1.84  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.64/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.64/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.64/1.84  tff('#skF_9', type, '#skF_9': $i).
% 4.64/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.64/1.84  tff('#skF_8', type, '#skF_8': $i).
% 4.64/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.64/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.84  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.64/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.64/1.84  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.64/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.64/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.64/1.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.64/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.64/1.84  
% 4.64/1.86  tff(f_125, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 4.64/1.86  tff(f_118, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.64/1.86  tff(f_109, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.64/1.86  tff(f_96, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.64/1.86  tff(f_73, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.64/1.86  tff(f_115, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.64/1.86  tff(f_79, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.64/1.86  tff(f_81, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.64/1.86  tff(f_111, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 4.64/1.86  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.64/1.86  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.64/1.86  tff(f_85, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.64/1.86  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.64/1.86  tff(f_89, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 4.64/1.86  tff(f_75, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.64/1.86  tff(c_78, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.64/1.86  tff(c_76, plain, (![A_42]: (~v1_xboole_0(k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.64/1.86  tff(c_199, plain, (![B_77, A_78]: (r2_hidden(B_77, A_78) | ~m1_subset_1(B_77, A_78) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.64/1.86  tff(c_52, plain, (![C_36, A_32]: (r1_tarski(C_36, A_32) | ~r2_hidden(C_36, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.64/1.86  tff(c_207, plain, (![B_77, A_32]: (r1_tarski(B_77, A_32) | ~m1_subset_1(B_77, k1_zfmisc_1(A_32)) | v1_xboole_0(k1_zfmisc_1(A_32)))), inference(resolution, [status(thm)], [c_199, c_52])).
% 4.64/1.86  tff(c_241, plain, (![B_82, A_83]: (r1_tarski(B_82, A_83) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)))), inference(negUnitSimplification, [status(thm)], [c_76, c_207])).
% 4.64/1.86  tff(c_250, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_78, c_241])).
% 4.64/1.86  tff(c_38, plain, (![B_20]: (r1_tarski(B_20, B_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.64/1.86  tff(c_54, plain, (![C_36, A_32]: (r2_hidden(C_36, k1_zfmisc_1(A_32)) | ~r1_tarski(C_36, A_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.64/1.86  tff(c_349, plain, (![B_91, A_92]: (m1_subset_1(B_91, A_92) | ~r2_hidden(B_91, A_92) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.64/1.86  tff(c_367, plain, (![C_36, A_32]: (m1_subset_1(C_36, k1_zfmisc_1(A_32)) | v1_xboole_0(k1_zfmisc_1(A_32)) | ~r1_tarski(C_36, A_32))), inference(resolution, [status(thm)], [c_54, c_349])).
% 4.64/1.86  tff(c_375, plain, (![C_36, A_32]: (m1_subset_1(C_36, k1_zfmisc_1(A_32)) | ~r1_tarski(C_36, A_32))), inference(negUnitSimplification, [status(thm)], [c_76, c_367])).
% 4.64/1.86  tff(c_580, plain, (![A_115, B_116]: (k4_xboole_0(A_115, B_116)=k3_subset_1(A_115, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.64/1.86  tff(c_659, plain, (![A_119, C_120]: (k4_xboole_0(A_119, C_120)=k3_subset_1(A_119, C_120) | ~r1_tarski(C_120, A_119))), inference(resolution, [status(thm)], [c_375, c_580])).
% 4.64/1.86  tff(c_672, plain, (![B_20]: (k4_xboole_0(B_20, B_20)=k3_subset_1(B_20, B_20))), inference(resolution, [status(thm)], [c_38, c_659])).
% 4.64/1.86  tff(c_109, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=A_55 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.64/1.86  tff(c_113, plain, (![B_20]: (k3_xboole_0(B_20, B_20)=B_20)), inference(resolution, [status(thm)], [c_38, c_109])).
% 4.64/1.86  tff(c_675, plain, (![B_121]: (k4_xboole_0(B_121, B_121)=k3_subset_1(B_121, B_121))), inference(resolution, [status(thm)], [c_38, c_659])).
% 4.64/1.86  tff(c_44, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.64/1.86  tff(c_692, plain, (![B_121]: (k4_xboole_0(B_121, k3_subset_1(B_121, B_121))=k3_xboole_0(B_121, B_121))), inference(superposition, [status(thm), theory('equality')], [c_675, c_44])).
% 4.64/1.86  tff(c_720, plain, (![B_123]: (k4_xboole_0(B_123, k3_subset_1(B_123, B_123))=B_123)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_692])).
% 4.64/1.86  tff(c_729, plain, (![B_123]: (k3_xboole_0(B_123, k3_subset_1(B_123, B_123))=k4_xboole_0(B_123, B_123))), inference(superposition, [status(thm), theory('equality')], [c_720, c_44])).
% 4.64/1.86  tff(c_737, plain, (![B_123]: (k3_xboole_0(B_123, k3_subset_1(B_123, B_123))=k3_subset_1(B_123, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_672, c_729])).
% 4.64/1.86  tff(c_708, plain, (![B_121]: (k4_xboole_0(B_121, k3_subset_1(B_121, B_121))=B_121)), inference(demodulation, [status(thm), theory('equality')], [c_113, c_692])).
% 4.64/1.86  tff(c_414, plain, (![A_96, B_97]: (k4_xboole_0(A_96, k4_xboole_0(A_96, B_97))=k3_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.64/1.86  tff(c_417, plain, (![A_96, B_97]: (k4_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k3_xboole_0(A_96, k4_xboole_0(A_96, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_414, c_44])).
% 4.64/1.86  tff(c_72, plain, (![A_39]: (k1_subset_1(A_39)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.64/1.86  tff(c_80, plain, (k1_subset_1('#skF_8')!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.64/1.86  tff(c_88, plain, (k1_xboole_0!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_80])).
% 4.64/1.86  tff(c_108, plain, (~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_88])).
% 4.64/1.86  tff(c_86, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_subset_1('#skF_8')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.64/1.86  tff(c_87, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_86])).
% 4.64/1.86  tff(c_123, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_108, c_87])).
% 4.64/1.86  tff(c_32, plain, (![A_17]: (r2_hidden('#skF_5'(A_17), A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.64/1.86  tff(c_124, plain, (![A_17]: (r2_hidden('#skF_5'(A_17), A_17) | A_17='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_32])).
% 4.64/1.86  tff(c_293, plain, (![D_85, A_86, B_87]: (r2_hidden(D_85, A_86) | ~r2_hidden(D_85, k3_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.64/1.86  tff(c_324, plain, (![A_86, B_87]: (r2_hidden('#skF_5'(k3_xboole_0(A_86, B_87)), A_86) | k3_xboole_0(A_86, B_87)='#skF_9')), inference(resolution, [status(thm)], [c_124, c_293])).
% 4.64/1.86  tff(c_48, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k4_xboole_0(A_27, B_28)!=A_27)), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.64/1.86  tff(c_456, plain, (![A_100, B_101, C_102]: (~r1_xboole_0(A_100, B_101) | ~r2_hidden(C_102, B_101) | ~r2_hidden(C_102, A_100))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.64/1.86  tff(c_1307, plain, (![C_166, B_167, A_168]: (~r2_hidden(C_166, B_167) | ~r2_hidden(C_166, A_168) | k4_xboole_0(A_168, B_167)!=A_168)), inference(resolution, [status(thm)], [c_48, c_456])).
% 4.64/1.86  tff(c_1662, plain, (![A_191, A_192]: (~r2_hidden('#skF_5'(A_191), A_192) | k4_xboole_0(A_192, A_191)!=A_192 | A_191='#skF_9')), inference(resolution, [status(thm)], [c_124, c_1307])).
% 4.64/1.86  tff(c_1665, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k3_xboole_0(A_86, B_87))!=A_86 | k3_xboole_0(A_86, B_87)='#skF_9')), inference(resolution, [status(thm)], [c_324, c_1662])).
% 4.64/1.86  tff(c_1797, plain, (![A_200, B_201]: (k3_xboole_0(A_200, k4_xboole_0(A_200, B_201))!=A_200 | k3_xboole_0(A_200, B_201)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_417, c_1665])).
% 4.64/1.86  tff(c_1818, plain, (![B_121]: (k3_xboole_0(B_121, B_121)!=B_121 | k3_xboole_0(B_121, k3_subset_1(B_121, B_121))='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_708, c_1797])).
% 4.64/1.86  tff(c_1845, plain, (![B_121]: (k3_subset_1(B_121, B_121)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_113, c_1818])).
% 4.64/1.86  tff(c_1865, plain, (![B_121]: (k4_xboole_0(B_121, '#skF_9')=B_121)), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_708])).
% 4.64/1.86  tff(c_600, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_580])).
% 4.64/1.86  tff(c_1948, plain, (k3_subset_1('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1865, c_600])).
% 4.64/1.86  tff(c_2103, plain, (~r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1948, c_108])).
% 4.64/1.86  tff(c_2106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_250, c_2103])).
% 4.64/1.86  tff(c_2107, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_88])).
% 4.64/1.86  tff(c_2210, plain, (![B_232, A_233]: (r2_hidden(B_232, A_233) | ~m1_subset_1(B_232, A_233) | v1_xboole_0(A_233))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.64/1.86  tff(c_2214, plain, (![B_232, A_32]: (r1_tarski(B_232, A_32) | ~m1_subset_1(B_232, k1_zfmisc_1(A_32)) | v1_xboole_0(k1_zfmisc_1(A_32)))), inference(resolution, [status(thm)], [c_2210, c_52])).
% 4.64/1.86  tff(c_2245, plain, (![B_236, A_237]: (r1_tarski(B_236, A_237) | ~m1_subset_1(B_236, k1_zfmisc_1(A_237)))), inference(negUnitSimplification, [status(thm)], [c_76, c_2214])).
% 4.64/1.86  tff(c_2254, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_78, c_2245])).
% 4.64/1.86  tff(c_42, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.64/1.86  tff(c_2261, plain, (k3_xboole_0('#skF_9', '#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_2254, c_42])).
% 4.64/1.86  tff(c_2371, plain, (![D_247, B_248, A_249]: (r2_hidden(D_247, B_248) | ~r2_hidden(D_247, k3_xboole_0(A_249, B_248)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.64/1.86  tff(c_2406, plain, (![D_250]: (r2_hidden(D_250, '#skF_8') | ~r2_hidden(D_250, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2261, c_2371])).
% 4.64/1.86  tff(c_2426, plain, (r2_hidden('#skF_5'('#skF_9'), '#skF_8') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_32, c_2406])).
% 4.64/1.86  tff(c_2433, plain, (r2_hidden('#skF_5'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2107, c_2426])).
% 4.64/1.86  tff(c_8, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, k3_xboole_0(A_6, B_7)) | ~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.64/1.86  tff(c_2130, plain, (![A_215, B_216]: (k3_xboole_0(A_215, B_216)=A_215 | ~r1_tarski(A_215, B_216))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.64/1.86  tff(c_2138, plain, (![B_20]: (k3_xboole_0(B_20, B_20)=B_20)), inference(resolution, [status(thm)], [c_38, c_2130])).
% 4.64/1.86  tff(c_2731, plain, (![A_278, B_279]: (k4_xboole_0(A_278, B_279)=k3_subset_1(A_278, B_279) | ~m1_subset_1(B_279, k1_zfmisc_1(A_278)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.64/1.86  tff(c_2758, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_2731])).
% 4.64/1.86  tff(c_2158, plain, (![A_220, C_221, B_222]: (r1_xboole_0(A_220, k4_xboole_0(C_221, B_222)) | ~r1_tarski(A_220, B_222))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.64/1.86  tff(c_46, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=A_27 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.64/1.86  tff(c_2162, plain, (![A_220, C_221, B_222]: (k4_xboole_0(A_220, k4_xboole_0(C_221, B_222))=A_220 | ~r1_tarski(A_220, B_222))), inference(resolution, [status(thm)], [c_2158, c_46])).
% 4.64/1.86  tff(c_2793, plain, (![A_281]: (k4_xboole_0(A_281, k3_subset_1('#skF_8', '#skF_9'))=A_281 | ~r1_tarski(A_281, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2758, c_2162])).
% 4.64/1.86  tff(c_40, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.64/1.86  tff(c_2265, plain, (k5_xboole_0('#skF_9', '#skF_9')=k4_xboole_0('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2261, c_40])).
% 4.64/1.86  tff(c_2186, plain, (![A_229, B_230]: (k5_xboole_0(A_229, k3_xboole_0(A_229, B_230))=k4_xboole_0(A_229, B_230))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.64/1.86  tff(c_2198, plain, (![B_20]: (k5_xboole_0(B_20, B_20)=k4_xboole_0(B_20, B_20))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_2186])).
% 4.64/1.86  tff(c_2273, plain, (k4_xboole_0('#skF_9', '#skF_9')=k4_xboole_0('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2265, c_2198])).
% 4.64/1.86  tff(c_2108, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_88])).
% 4.64/1.86  tff(c_2137, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_2108, c_2130])).
% 4.64/1.86  tff(c_2195, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k5_xboole_0('#skF_9', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2137, c_2186])).
% 4.64/1.86  tff(c_2476, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))=k4_xboole_0('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2273, c_2198, c_2195])).
% 4.64/1.86  tff(c_2805, plain, (k4_xboole_0('#skF_9', '#skF_8')='#skF_9' | ~r1_tarski('#skF_9', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2793, c_2476])).
% 4.64/1.86  tff(c_2823, plain, (k4_xboole_0('#skF_9', '#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2805])).
% 4.64/1.86  tff(c_2963, plain, (![A_288]: (k4_xboole_0(A_288, '#skF_9')=A_288 | ~r1_tarski(A_288, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2823, c_2162])).
% 4.64/1.86  tff(c_2983, plain, (k4_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_38, c_2963])).
% 4.64/1.86  tff(c_2984, plain, (k3_subset_1('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2983, c_2758])).
% 4.64/1.86  tff(c_2765, plain, (k4_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2758, c_44])).
% 4.64/1.86  tff(c_3022, plain, (k4_xboole_0('#skF_8', '#skF_8')=k3_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2984, c_2765])).
% 4.64/1.86  tff(c_3048, plain, (k4_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_9'))=k3_xboole_0('#skF_8', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3022, c_44])).
% 4.64/1.86  tff(c_3054, plain, (k4_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2138, c_3048])).
% 4.64/1.86  tff(c_50, plain, (![A_29, C_31, B_30]: (r1_xboole_0(A_29, k4_xboole_0(C_31, B_30)) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.64/1.86  tff(c_3121, plain, (![A_296]: (r1_xboole_0(A_296, '#skF_8') | ~r1_tarski(A_296, k3_xboole_0('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_3054, c_50])).
% 4.64/1.86  tff(c_3141, plain, (r1_xboole_0(k3_xboole_0('#skF_8', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_38, c_3121])).
% 4.64/1.86  tff(c_26, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, B_13) | ~r2_hidden(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.64/1.86  tff(c_3171, plain, (![C_297]: (~r2_hidden(C_297, '#skF_8') | ~r2_hidden(C_297, k3_xboole_0('#skF_8', '#skF_9')))), inference(resolution, [status(thm)], [c_3141, c_26])).
% 4.64/1.86  tff(c_3265, plain, (![D_300]: (~r2_hidden(D_300, '#skF_9') | ~r2_hidden(D_300, '#skF_8'))), inference(resolution, [status(thm)], [c_8, c_3171])).
% 4.64/1.86  tff(c_3297, plain, (~r2_hidden('#skF_5'('#skF_9'), '#skF_8') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_32, c_3265])).
% 4.64/1.86  tff(c_3310, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2433, c_3297])).
% 4.64/1.86  tff(c_3312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2107, c_3310])).
% 4.64/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.86  
% 4.64/1.86  Inference rules
% 4.64/1.86  ----------------------
% 4.64/1.86  #Ref     : 0
% 4.64/1.86  #Sup     : 750
% 4.64/1.86  #Fact    : 0
% 4.64/1.86  #Define  : 0
% 4.64/1.86  #Split   : 8
% 4.64/1.86  #Chain   : 0
% 4.64/1.86  #Close   : 0
% 4.64/1.86  
% 4.64/1.86  Ordering : KBO
% 4.64/1.86  
% 4.64/1.86  Simplification rules
% 4.64/1.86  ----------------------
% 4.64/1.86  #Subsume      : 62
% 4.64/1.86  #Demod        : 188
% 4.64/1.86  #Tautology    : 230
% 4.64/1.86  #SimpNegUnit  : 21
% 4.64/1.86  #BackRed      : 46
% 4.64/1.86  
% 4.64/1.86  #Partial instantiations: 0
% 4.64/1.86  #Strategies tried      : 1
% 4.64/1.86  
% 4.64/1.86  Timing (in seconds)
% 4.64/1.86  ----------------------
% 4.64/1.87  Preprocessing        : 0.35
% 4.64/1.87  Parsing              : 0.18
% 4.64/1.87  CNF conversion       : 0.03
% 4.64/1.87  Main loop            : 0.74
% 4.64/1.87  Inferencing          : 0.26
% 4.64/1.87  Reduction            : 0.22
% 4.64/1.87  Demodulation         : 0.15
% 4.64/1.87  BG Simplification    : 0.04
% 4.64/1.87  Subsumption          : 0.15
% 4.64/1.87  Abstraction          : 0.04
% 4.64/1.87  MUC search           : 0.00
% 4.64/1.87  Cooper               : 0.00
% 4.64/1.87  Total                : 1.13
% 4.64/1.87  Index Insertion      : 0.00
% 4.64/1.87  Index Deletion       : 0.00
% 4.64/1.87  Index Matching       : 0.00
% 4.64/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
