%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:37 EST 2020

% Result     : Theorem 14.92s
% Output     : CNFRefutation 15.01s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 307 expanded)
%              Number of leaves         :   30 ( 113 expanded)
%              Depth                    :   13
%              Number of atoms          :  166 ( 590 expanded)
%              Number of equality atoms :   54 ( 150 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_177,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_145,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_141,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_156,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_73,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_167,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( ( k1_relat_1(A) = k1_xboole_0
              & k1_relat_1(B) = k1_xboole_0 )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_relat_1)).

tff(c_160,plain,(
    ! [A_73,B_74] :
      ( r1_xboole_0(A_73,B_74)
      | k3_xboole_0(A_73,B_74) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_176,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_160,c_60])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_52,plain,(
    ! [A_47,B_48] :
      ( v1_relat_1(k3_xboole_0(A_47,B_48))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_62,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_104,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    k3_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_104])).

tff(c_440,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,k3_xboole_0(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_450,plain,(
    ! [C_94] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_4'))
      | ~ r2_hidden(C_94,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_440])).

tff(c_461,plain,(
    ! [C_94] : ~ r2_hidden(C_94,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_450])).

tff(c_50,plain,(
    ! [A_45,B_46] : r1_xboole_0(k4_xboole_0(A_45,k3_xboole_0(A_45,B_46)),B_46) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_583,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_xboole_0(A_107,k4_xboole_0(B_108,C_109))
      | ~ r1_xboole_0(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_24,plain,(
    ! [A_19] :
      ( ~ r1_xboole_0(A_19,A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5802,plain,(
    ! [B_317,C_318] :
      ( k4_xboole_0(B_317,C_318) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(B_317,C_318),B_317) ) ),
    inference(resolution,[status(thm)],[c_583,c_24])).

tff(c_6228,plain,(
    ! [B_323] : k4_xboole_0(B_323,k3_xboole_0(B_323,B_323)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_5802])).

tff(c_220,plain,(
    ! [A_76,B_77] :
      ( r1_xboole_0(A_76,B_77)
      | k4_xboole_0(A_76,B_77) != A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_389,plain,(
    ! [B_88,A_89] :
      ( r1_xboole_0(B_88,A_89)
      | k4_xboole_0(A_89,B_88) != A_89 ) ),
    inference(resolution,[status(thm)],[c_220,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_406,plain,(
    ! [B_88,A_89] :
      ( k3_xboole_0(B_88,A_89) = k1_xboole_0
      | k4_xboole_0(A_89,B_88) != A_89 ) ),
    inference(resolution,[status(thm)],[c_389,c_2])).

tff(c_7633,plain,(
    ! [B_348] :
      ( k3_xboole_0(k3_xboole_0(B_348,B_348),B_348) = k1_xboole_0
      | k1_xboole_0 != B_348 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6228,c_406])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),k3_xboole_0(A_10,B_11))
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7703,plain,(
    ! [B_348] :
      ( r2_hidden('#skF_2'(k3_xboole_0(B_348,B_348),B_348),k1_xboole_0)
      | r1_xboole_0(k3_xboole_0(B_348,B_348),B_348)
      | k1_xboole_0 != B_348 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7633,c_14])).

tff(c_7911,plain,(
    ! [B_352] :
      ( r1_xboole_0(k3_xboole_0(B_352,B_352),B_352)
      | k1_xboole_0 != B_352 ) ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_7703])).

tff(c_466,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_xboole_0(A_95,B_96)
      | r1_xboole_0(A_95,k3_xboole_0(B_96,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_494,plain,(
    ! [B_96,C_97] :
      ( k3_xboole_0(B_96,C_97) = k1_xboole_0
      | ~ r1_xboole_0(k3_xboole_0(B_96,C_97),B_96) ) ),
    inference(resolution,[status(thm)],[c_466,c_24])).

tff(c_7987,plain,(
    ! [B_353] :
      ( k3_xboole_0(B_353,B_353) = k1_xboole_0
      | k1_xboole_0 != B_353 ) ),
    inference(resolution,[status(thm)],[c_7911,c_494])).

tff(c_174,plain,(
    ! [B_74,A_73] :
      ( r1_xboole_0(B_74,A_73)
      | k3_xboole_0(A_73,B_74) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_160,c_6])).

tff(c_493,plain,(
    ! [B_96,C_97,A_95] :
      ( r1_xboole_0(k3_xboole_0(B_96,C_97),A_95)
      | ~ r1_xboole_0(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_466,c_6])).

tff(c_3324,plain,(
    ! [B_249,C_250] :
      ( k3_xboole_0(B_249,C_250) = k1_xboole_0
      | ~ r1_xboole_0(k3_xboole_0(B_249,C_250),B_249) ) ),
    inference(resolution,[status(thm)],[c_466,c_24])).

tff(c_3461,plain,(
    ! [A_251,C_252] :
      ( k3_xboole_0(A_251,C_252) = k1_xboole_0
      | ~ r1_xboole_0(A_251,A_251) ) ),
    inference(resolution,[status(thm)],[c_493,c_3324])).

tff(c_3568,plain,(
    ! [A_73,C_252] :
      ( k3_xboole_0(A_73,C_252) = k1_xboole_0
      | k3_xboole_0(A_73,A_73) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_174,c_3461])).

tff(c_9425,plain,(
    ! [C_252] : k3_xboole_0(k1_xboole_0,C_252) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7987,c_3568])).

tff(c_66,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_76,plain,(
    ! [B_60,A_61] :
      ( r1_xboole_0(B_60,A_61)
      | ~ r1_xboole_0(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_81,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_76])).

tff(c_121,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_104])).

tff(c_3587,plain,(
    ! [A_255,B_256] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_255,B_256)),k3_xboole_0(k1_relat_1(A_255),k1_relat_1(B_256)))
      | ~ v1_relat_1(B_256)
      | ~ v1_relat_1(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3610,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_4','#skF_3')),k1_xboole_0)
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_3587])).

tff(c_3626,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_4','#skF_3')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_3610])).

tff(c_20,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_268,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = A_80
      | ~ r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_296,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(resolution,[status(thm)],[c_20,c_268])).

tff(c_614,plain,(
    ! [A_110,C_111,B_112] :
      ( r1_xboole_0(A_110,k4_xboole_0(C_111,B_112))
      | ~ r1_tarski(A_110,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_696,plain,(
    ! [A_116,A_117] :
      ( r1_xboole_0(A_116,A_117)
      | ~ r1_tarski(A_116,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_614])).

tff(c_725,plain,(
    ! [A_117] :
      ( k1_xboole_0 = A_117
      | ~ r1_tarski(A_117,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_696,c_24])).

tff(c_3744,plain,(
    k1_relat_1(k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3626,c_725])).

tff(c_125,plain,(
    ! [A_71] : k3_xboole_0(A_71,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_104])).

tff(c_133,plain,(
    ! [A_71] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_52])).

tff(c_177,plain,(
    ! [A_71] : ~ v1_relat_1(A_71) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_64])).

tff(c_183,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_124,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_104])).

tff(c_3622,plain,(
    ! [A_18] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(A_18),k1_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_3587])).

tff(c_44212,plain,(
    ! [A_896] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(A_896),k1_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(A_896) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_3622])).

tff(c_44269,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_xboole_0,k1_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3744,c_44212])).

tff(c_44296,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9425,c_44269])).

tff(c_44298,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44296])).

tff(c_44307,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_44298])).

tff(c_44315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44307])).

tff(c_44316,plain,(
    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_44296])).

tff(c_44426,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44316,c_725])).

tff(c_3616,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_3','#skF_4')),k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_3587])).

tff(c_3628,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_3','#skF_4')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3616])).

tff(c_3660,plain,(
    k1_relat_1(k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3628,c_725])).

tff(c_3259,plain,(
    ! [B_236,A_237] :
      ( B_236 = A_237
      | k1_relat_1(B_236) != k1_xboole_0
      | k1_relat_1(A_237) != k1_xboole_0
      | ~ v1_relat_1(B_236)
      | ~ v1_relat_1(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_32454,plain,(
    ! [A_762,B_763,A_764] :
      ( k3_xboole_0(A_762,B_763) = A_764
      | k1_relat_1(k3_xboole_0(A_762,B_763)) != k1_xboole_0
      | k1_relat_1(A_764) != k1_xboole_0
      | ~ v1_relat_1(A_764)
      | ~ v1_relat_1(A_762) ) ),
    inference(resolution,[status(thm)],[c_52,c_3259])).

tff(c_32504,plain,(
    ! [A_764] :
      ( k3_xboole_0('#skF_3','#skF_4') = A_764
      | k1_relat_1(A_764) != k1_xboole_0
      | ~ v1_relat_1(A_764)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_32454])).

tff(c_55833,plain,(
    ! [A_1038] :
      ( k3_xboole_0('#skF_3','#skF_4') = A_1038
      | k1_relat_1(A_1038) != k1_xboole_0
      | ~ v1_relat_1(A_1038) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32504])).

tff(c_55839,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_183,c_55833])).

tff(c_55857,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44426,c_55839])).

tff(c_55859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_55857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.92/7.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.92/7.57  
% 14.92/7.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.92/7.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 14.92/7.58  
% 14.92/7.58  %Foreground sorts:
% 14.92/7.58  
% 14.92/7.58  
% 14.92/7.58  %Background operators:
% 14.92/7.58  
% 14.92/7.58  
% 14.92/7.58  %Foreground operators:
% 14.92/7.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.92/7.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.92/7.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.92/7.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.92/7.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.92/7.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.92/7.58  tff('#skF_3', type, '#skF_3': $i).
% 14.92/7.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.92/7.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.92/7.58  tff('#skF_4', type, '#skF_4': $i).
% 14.92/7.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.92/7.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.92/7.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.92/7.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.92/7.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.92/7.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.92/7.58  
% 15.01/7.59  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.01/7.59  tff(f_177, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 15.01/7.59  tff(f_145, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 15.01/7.59  tff(f_65, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 15.01/7.59  tff(f_141, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 15.01/7.59  tff(f_123, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 15.01/7.59  tff(f_85, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 15.01/7.59  tff(f_131, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 15.01/7.59  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 15.01/7.59  tff(f_115, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 15.01/7.59  tff(f_156, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 15.01/7.59  tff(f_73, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 15.01/7.59  tff(f_135, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 15.01/7.59  tff(f_167, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k1_relat_1(A) = k1_xboole_0) & (k1_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t196_relat_1)).
% 15.01/7.59  tff(c_160, plain, (![A_73, B_74]: (r1_xboole_0(A_73, B_74) | k3_xboole_0(A_73, B_74)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.01/7.59  tff(c_60, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.01/7.59  tff(c_176, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_160, c_60])).
% 15.01/7.59  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.01/7.59  tff(c_52, plain, (![A_47, B_48]: (v1_relat_1(k3_xboole_0(A_47, B_48)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_145])).
% 15.01/7.59  tff(c_62, plain, (r1_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.01/7.59  tff(c_104, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.01/7.59  tff(c_123, plain, (k3_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_104])).
% 15.01/7.59  tff(c_440, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, k3_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.01/7.59  tff(c_450, plain, (![C_94]: (~r1_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_4')) | ~r2_hidden(C_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_123, c_440])).
% 15.01/7.59  tff(c_461, plain, (![C_94]: (~r2_hidden(C_94, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_450])).
% 15.01/7.59  tff(c_50, plain, (![A_45, B_46]: (r1_xboole_0(k4_xboole_0(A_45, k3_xboole_0(A_45, B_46)), B_46))), inference(cnfTransformation, [status(thm)], [f_141])).
% 15.01/7.59  tff(c_583, plain, (![A_107, B_108, C_109]: (r1_xboole_0(A_107, k4_xboole_0(B_108, C_109)) | ~r1_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_123])).
% 15.01/7.59  tff(c_24, plain, (![A_19]: (~r1_xboole_0(A_19, A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.01/7.59  tff(c_5802, plain, (![B_317, C_318]: (k4_xboole_0(B_317, C_318)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(B_317, C_318), B_317))), inference(resolution, [status(thm)], [c_583, c_24])).
% 15.01/7.59  tff(c_6228, plain, (![B_323]: (k4_xboole_0(B_323, k3_xboole_0(B_323, B_323))=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_5802])).
% 15.01/7.59  tff(c_220, plain, (![A_76, B_77]: (r1_xboole_0(A_76, B_77) | k4_xboole_0(A_76, B_77)!=A_76)), inference(cnfTransformation, [status(thm)], [f_131])).
% 15.01/7.59  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.01/7.59  tff(c_389, plain, (![B_88, A_89]: (r1_xboole_0(B_88, A_89) | k4_xboole_0(A_89, B_88)!=A_89)), inference(resolution, [status(thm)], [c_220, c_6])).
% 15.01/7.59  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.01/7.59  tff(c_406, plain, (![B_88, A_89]: (k3_xboole_0(B_88, A_89)=k1_xboole_0 | k4_xboole_0(A_89, B_88)!=A_89)), inference(resolution, [status(thm)], [c_389, c_2])).
% 15.01/7.59  tff(c_7633, plain, (![B_348]: (k3_xboole_0(k3_xboole_0(B_348, B_348), B_348)=k1_xboole_0 | k1_xboole_0!=B_348)), inference(superposition, [status(thm), theory('equality')], [c_6228, c_406])).
% 15.01/7.59  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), k3_xboole_0(A_10, B_11)) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.01/7.59  tff(c_7703, plain, (![B_348]: (r2_hidden('#skF_2'(k3_xboole_0(B_348, B_348), B_348), k1_xboole_0) | r1_xboole_0(k3_xboole_0(B_348, B_348), B_348) | k1_xboole_0!=B_348)), inference(superposition, [status(thm), theory('equality')], [c_7633, c_14])).
% 15.01/7.59  tff(c_7911, plain, (![B_352]: (r1_xboole_0(k3_xboole_0(B_352, B_352), B_352) | k1_xboole_0!=B_352)), inference(negUnitSimplification, [status(thm)], [c_461, c_7703])).
% 15.01/7.59  tff(c_466, plain, (![A_95, B_96, C_97]: (~r1_xboole_0(A_95, B_96) | r1_xboole_0(A_95, k3_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 15.01/7.59  tff(c_494, plain, (![B_96, C_97]: (k3_xboole_0(B_96, C_97)=k1_xboole_0 | ~r1_xboole_0(k3_xboole_0(B_96, C_97), B_96))), inference(resolution, [status(thm)], [c_466, c_24])).
% 15.01/7.59  tff(c_7987, plain, (![B_353]: (k3_xboole_0(B_353, B_353)=k1_xboole_0 | k1_xboole_0!=B_353)), inference(resolution, [status(thm)], [c_7911, c_494])).
% 15.01/7.59  tff(c_174, plain, (![B_74, A_73]: (r1_xboole_0(B_74, A_73) | k3_xboole_0(A_73, B_74)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_160, c_6])).
% 15.01/7.59  tff(c_493, plain, (![B_96, C_97, A_95]: (r1_xboole_0(k3_xboole_0(B_96, C_97), A_95) | ~r1_xboole_0(A_95, B_96))), inference(resolution, [status(thm)], [c_466, c_6])).
% 15.01/7.59  tff(c_3324, plain, (![B_249, C_250]: (k3_xboole_0(B_249, C_250)=k1_xboole_0 | ~r1_xboole_0(k3_xboole_0(B_249, C_250), B_249))), inference(resolution, [status(thm)], [c_466, c_24])).
% 15.01/7.59  tff(c_3461, plain, (![A_251, C_252]: (k3_xboole_0(A_251, C_252)=k1_xboole_0 | ~r1_xboole_0(A_251, A_251))), inference(resolution, [status(thm)], [c_493, c_3324])).
% 15.01/7.59  tff(c_3568, plain, (![A_73, C_252]: (k3_xboole_0(A_73, C_252)=k1_xboole_0 | k3_xboole_0(A_73, A_73)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_174, c_3461])).
% 15.01/7.59  tff(c_9425, plain, (![C_252]: (k3_xboole_0(k1_xboole_0, C_252)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7987, c_3568])).
% 15.01/7.59  tff(c_66, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.01/7.59  tff(c_76, plain, (![B_60, A_61]: (r1_xboole_0(B_60, A_61) | ~r1_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.01/7.59  tff(c_81, plain, (r1_xboole_0(k1_relat_1('#skF_4'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_76])).
% 15.01/7.59  tff(c_121, plain, (k3_xboole_0(k1_relat_1('#skF_4'), k1_relat_1('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_81, c_104])).
% 15.01/7.59  tff(c_3587, plain, (![A_255, B_256]: (r1_tarski(k1_relat_1(k3_xboole_0(A_255, B_256)), k3_xboole_0(k1_relat_1(A_255), k1_relat_1(B_256))) | ~v1_relat_1(B_256) | ~v1_relat_1(A_255))), inference(cnfTransformation, [status(thm)], [f_156])).
% 15.01/7.59  tff(c_3610, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k1_xboole_0) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_3587])).
% 15.01/7.59  tff(c_3626, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_3610])).
% 15.01/7.59  tff(c_20, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.01/7.59  tff(c_268, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=A_80 | ~r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_131])).
% 15.01/7.59  tff(c_296, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(resolution, [status(thm)], [c_20, c_268])).
% 15.01/7.59  tff(c_614, plain, (![A_110, C_111, B_112]: (r1_xboole_0(A_110, k4_xboole_0(C_111, B_112)) | ~r1_tarski(A_110, B_112))), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.01/7.59  tff(c_696, plain, (![A_116, A_117]: (r1_xboole_0(A_116, A_117) | ~r1_tarski(A_116, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_296, c_614])).
% 15.01/7.59  tff(c_725, plain, (![A_117]: (k1_xboole_0=A_117 | ~r1_tarski(A_117, k1_xboole_0))), inference(resolution, [status(thm)], [c_696, c_24])).
% 15.01/7.59  tff(c_3744, plain, (k1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_3626, c_725])).
% 15.01/7.59  tff(c_125, plain, (![A_71]: (k3_xboole_0(A_71, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_104])).
% 15.01/7.59  tff(c_133, plain, (![A_71]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_125, c_52])).
% 15.01/7.59  tff(c_177, plain, (![A_71]: (~v1_relat_1(A_71))), inference(splitLeft, [status(thm)], [c_133])).
% 15.01/7.59  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_64])).
% 15.01/7.59  tff(c_183, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_133])).
% 15.01/7.59  tff(c_124, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_104])).
% 15.01/7.59  tff(c_3622, plain, (![A_18]: (r1_tarski(k1_relat_1(k1_xboole_0), k3_xboole_0(k1_relat_1(A_18), k1_relat_1(k1_xboole_0))) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_124, c_3587])).
% 15.01/7.59  tff(c_44212, plain, (![A_896]: (r1_tarski(k1_relat_1(k1_xboole_0), k3_xboole_0(k1_relat_1(A_896), k1_relat_1(k1_xboole_0))) | ~v1_relat_1(A_896))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_3622])).
% 15.01/7.59  tff(c_44269, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k3_xboole_0(k1_xboole_0, k1_relat_1(k1_xboole_0))) | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3744, c_44212])).
% 15.01/7.59  tff(c_44296, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9425, c_44269])).
% 15.01/7.59  tff(c_44298, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44296])).
% 15.01/7.59  tff(c_44307, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_44298])).
% 15.01/7.59  tff(c_44315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_44307])).
% 15.01/7.59  tff(c_44316, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0)), inference(splitRight, [status(thm)], [c_44296])).
% 15.01/7.59  tff(c_44426, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44316, c_725])).
% 15.01/7.59  tff(c_3616, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k1_xboole_0) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_123, c_3587])).
% 15.01/7.60  tff(c_3628, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3616])).
% 15.01/7.60  tff(c_3660, plain, (k1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_3628, c_725])).
% 15.01/7.60  tff(c_3259, plain, (![B_236, A_237]: (B_236=A_237 | k1_relat_1(B_236)!=k1_xboole_0 | k1_relat_1(A_237)!=k1_xboole_0 | ~v1_relat_1(B_236) | ~v1_relat_1(A_237))), inference(cnfTransformation, [status(thm)], [f_167])).
% 15.01/7.60  tff(c_32454, plain, (![A_762, B_763, A_764]: (k3_xboole_0(A_762, B_763)=A_764 | k1_relat_1(k3_xboole_0(A_762, B_763))!=k1_xboole_0 | k1_relat_1(A_764)!=k1_xboole_0 | ~v1_relat_1(A_764) | ~v1_relat_1(A_762))), inference(resolution, [status(thm)], [c_52, c_3259])).
% 15.01/7.60  tff(c_32504, plain, (![A_764]: (k3_xboole_0('#skF_3', '#skF_4')=A_764 | k1_relat_1(A_764)!=k1_xboole_0 | ~v1_relat_1(A_764) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3660, c_32454])).
% 15.01/7.60  tff(c_55833, plain, (![A_1038]: (k3_xboole_0('#skF_3', '#skF_4')=A_1038 | k1_relat_1(A_1038)!=k1_xboole_0 | ~v1_relat_1(A_1038))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_32504])).
% 15.01/7.60  tff(c_55839, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_183, c_55833])).
% 15.01/7.60  tff(c_55857, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44426, c_55839])).
% 15.01/7.60  tff(c_55859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_55857])).
% 15.01/7.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.01/7.60  
% 15.01/7.60  Inference rules
% 15.01/7.60  ----------------------
% 15.01/7.60  #Ref     : 0
% 15.01/7.60  #Sup     : 13519
% 15.01/7.60  #Fact    : 0
% 15.01/7.60  #Define  : 0
% 15.01/7.60  #Split   : 8
% 15.01/7.60  #Chain   : 0
% 15.01/7.60  #Close   : 0
% 15.01/7.60  
% 15.01/7.60  Ordering : KBO
% 15.01/7.60  
% 15.01/7.60  Simplification rules
% 15.01/7.60  ----------------------
% 15.01/7.60  #Subsume      : 4813
% 15.01/7.60  #Demod        : 5844
% 15.01/7.60  #Tautology    : 4874
% 15.01/7.60  #SimpNegUnit  : 95
% 15.01/7.60  #BackRed      : 7
% 15.01/7.60  
% 15.01/7.60  #Partial instantiations: 0
% 15.01/7.60  #Strategies tried      : 1
% 15.01/7.60  
% 15.01/7.60  Timing (in seconds)
% 15.01/7.60  ----------------------
% 15.01/7.60  Preprocessing        : 0.32
% 15.01/7.60  Parsing              : 0.18
% 15.01/7.60  CNF conversion       : 0.02
% 15.01/7.60  Main loop            : 6.51
% 15.01/7.60  Inferencing          : 1.08
% 15.01/7.60  Reduction            : 2.40
% 15.01/7.60  Demodulation         : 1.86
% 15.01/7.60  BG Simplification    : 0.12
% 15.01/7.60  Subsumption          : 2.54
% 15.01/7.60  Abstraction          : 0.17
% 15.01/7.60  MUC search           : 0.00
% 15.01/7.60  Cooper               : 0.00
% 15.01/7.60  Total                : 6.87
% 15.01/7.60  Index Insertion      : 0.00
% 15.01/7.60  Index Deletion       : 0.00
% 15.01/7.60  Index Matching       : 0.00
% 15.01/7.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
