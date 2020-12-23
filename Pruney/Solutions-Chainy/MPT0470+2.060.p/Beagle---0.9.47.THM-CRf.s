%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:09 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 115 expanded)
%              Number of leaves         :   29 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  140 ( 212 expanded)
%              Number of equality atoms :   37 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_103,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_36,plain,
    ( k5_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_65,plain,(
    k5_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_54,plain,(
    ! [A_25] :
      ( v1_relat_1(A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k5_relat_1(A_13,B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_133,plain,(
    ! [A_55,B_56] :
      ( k1_relat_1(k5_relat_1(A_55,B_56)) = k1_relat_1(A_55)
      | ~ r1_tarski(k2_relat_1(A_55),k1_relat_1(B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_139,plain,(
    ! [B_56] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_56)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_133])).

tff(c_204,plain,(
    ! [B_64] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_64)) = k1_xboole_0
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18,c_34,c_139])).

tff(c_24,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(k1_relat_1(A_15))
      | ~ v1_relat_1(A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_213,plain,(
    ! [B_64] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_64))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_24])).

tff(c_221,plain,(
    ! [B_65] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_65))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_213])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_230,plain,(
    ! [B_66] :
      ( k5_relat_1(k1_xboole_0,B_66) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_221,c_8])).

tff(c_234,plain,(
    ! [B_14] :
      ( k5_relat_1(k1_xboole_0,B_14) = k1_xboole_0
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_230])).

tff(c_272,plain,(
    ! [B_68] :
      ( k5_relat_1(k1_xboole_0,B_68) = k1_xboole_0
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_234])).

tff(c_281,plain,(
    k5_relat_1(k1_xboole_0,'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_272])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_281])).

tff(c_288,plain,(
    k5_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_300,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_304,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_300])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_326,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,B_84)
      | ~ r2_hidden(C_85,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_350,plain,(
    ! [C_89,B_90,A_91] :
      ( ~ r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | k3_xboole_0(A_91,B_90) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_326])).

tff(c_366,plain,(
    ! [A_93,B_94,A_95] :
      ( ~ r2_hidden('#skF_1'(A_93,B_94),A_95)
      | k3_xboole_0(A_95,B_94) != k1_xboole_0
      | r1_xboole_0(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_12,c_350])).

tff(c_375,plain,(
    ! [B_96,A_97] :
      ( k3_xboole_0(B_96,B_96) != k1_xboole_0
      | r1_xboole_0(A_97,B_96) ) ),
    inference(resolution,[status(thm)],[c_12,c_366])).

tff(c_391,plain,(
    ! [A_100] : r1_xboole_0(A_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_375])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_398,plain,(
    ! [A_100] : k3_xboole_0(A_100,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_391,c_2])).

tff(c_330,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_86,B_87)),k2_relat_1(B_87))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_339,plain,(
    ! [A_86] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_86,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_330])).

tff(c_345,plain,(
    ! [A_88] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_88,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_339])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_349,plain,(
    ! [A_88] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_88,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_88,k1_xboole_0))
      | ~ v1_relat_1(A_88) ) ),
    inference(resolution,[status(thm)],[c_345,c_16])).

tff(c_474,plain,(
    ! [A_108] :
      ( k2_relat_1(k5_relat_1(A_108,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_349])).

tff(c_26,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(k2_relat_1(A_16))
      | ~ v1_relat_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_492,plain,(
    ! [A_108] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_108,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_108,k1_xboole_0))
      | ~ v1_relat_1(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_26])).

tff(c_742,plain,(
    ! [A_117] :
      ( ~ v1_relat_1(k5_relat_1(A_117,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_117,k1_xboole_0))
      | ~ v1_relat_1(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_492])).

tff(c_756,plain,(
    ! [A_118] :
      ( k5_relat_1(A_118,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_118,k1_xboole_0))
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_742,c_8])).

tff(c_763,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_22,c_756])).

tff(c_769,plain,(
    ! [A_119] :
      ( k5_relat_1(A_119,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_763])).

tff(c_778,plain,(
    k5_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_769])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:44:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.50  
% 2.69/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.69/1.50  
% 2.69/1.50  %Foreground sorts:
% 2.69/1.50  
% 2.69/1.50  
% 2.69/1.50  %Background operators:
% 2.69/1.50  
% 2.69/1.50  
% 2.69/1.50  %Foreground operators:
% 2.69/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.69/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.50  
% 2.69/1.52  tff(f_110, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.69/1.52  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.69/1.52  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.69/1.52  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.69/1.52  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.69/1.52  tff(f_103, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.69/1.52  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.69/1.52  tff(f_76, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.69/1.52  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.69/1.52  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.69/1.52  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.69/1.52  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.69/1.52  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.69/1.52  tff(f_84, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.69/1.52  tff(c_36, plain, (k5_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.69/1.52  tff(c_65, plain, (k5_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.69/1.52  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.69/1.52  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.69/1.52  tff(c_54, plain, (![A_25]: (v1_relat_1(A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.52  tff(c_58, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_54])).
% 2.69/1.52  tff(c_22, plain, (![A_13, B_14]: (v1_relat_1(k5_relat_1(A_13, B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.52  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.69/1.52  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.69/1.52  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.69/1.52  tff(c_133, plain, (![A_55, B_56]: (k1_relat_1(k5_relat_1(A_55, B_56))=k1_relat_1(A_55) | ~r1_tarski(k2_relat_1(A_55), k1_relat_1(B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.69/1.52  tff(c_139, plain, (![B_56]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_56))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_133])).
% 2.69/1.52  tff(c_204, plain, (![B_64]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_64))=k1_xboole_0 | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18, c_34, c_139])).
% 2.69/1.52  tff(c_24, plain, (![A_15]: (~v1_xboole_0(k1_relat_1(A_15)) | ~v1_relat_1(A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.52  tff(c_213, plain, (![B_64]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_64)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_64)) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_204, c_24])).
% 2.69/1.52  tff(c_221, plain, (![B_65]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_65)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_65)) | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_213])).
% 2.69/1.52  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.69/1.52  tff(c_230, plain, (![B_66]: (k5_relat_1(k1_xboole_0, B_66)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_66)) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_221, c_8])).
% 2.69/1.52  tff(c_234, plain, (![B_14]: (k5_relat_1(k1_xboole_0, B_14)=k1_xboole_0 | ~v1_relat_1(B_14) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_230])).
% 2.69/1.52  tff(c_272, plain, (![B_68]: (k5_relat_1(k1_xboole_0, B_68)=k1_xboole_0 | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_234])).
% 2.69/1.52  tff(c_281, plain, (k5_relat_1(k1_xboole_0, '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_272])).
% 2.69/1.52  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_281])).
% 2.69/1.52  tff(c_288, plain, (k5_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.69/1.52  tff(c_300, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.52  tff(c_304, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_300])).
% 2.69/1.52  tff(c_12, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.52  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.52  tff(c_326, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, B_84) | ~r2_hidden(C_85, A_83))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.52  tff(c_350, plain, (![C_89, B_90, A_91]: (~r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | k3_xboole_0(A_91, B_90)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_326])).
% 2.69/1.52  tff(c_366, plain, (![A_93, B_94, A_95]: (~r2_hidden('#skF_1'(A_93, B_94), A_95) | k3_xboole_0(A_95, B_94)!=k1_xboole_0 | r1_xboole_0(A_93, B_94))), inference(resolution, [status(thm)], [c_12, c_350])).
% 2.69/1.52  tff(c_375, plain, (![B_96, A_97]: (k3_xboole_0(B_96, B_96)!=k1_xboole_0 | r1_xboole_0(A_97, B_96))), inference(resolution, [status(thm)], [c_12, c_366])).
% 2.69/1.52  tff(c_391, plain, (![A_100]: (r1_xboole_0(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_304, c_375])).
% 2.69/1.52  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.52  tff(c_398, plain, (![A_100]: (k3_xboole_0(A_100, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_391, c_2])).
% 2.69/1.52  tff(c_330, plain, (![A_86, B_87]: (r1_tarski(k2_relat_1(k5_relat_1(A_86, B_87)), k2_relat_1(B_87)) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.69/1.52  tff(c_339, plain, (![A_86]: (r1_tarski(k2_relat_1(k5_relat_1(A_86, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_32, c_330])).
% 2.69/1.52  tff(c_345, plain, (![A_88]: (r1_tarski(k2_relat_1(k5_relat_1(A_88, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_339])).
% 2.69/1.52  tff(c_16, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.52  tff(c_349, plain, (![A_88]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_88, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_88, k1_xboole_0)) | ~v1_relat_1(A_88))), inference(resolution, [status(thm)], [c_345, c_16])).
% 2.69/1.52  tff(c_474, plain, (![A_108]: (k2_relat_1(k5_relat_1(A_108, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_349])).
% 2.69/1.52  tff(c_26, plain, (![A_16]: (~v1_xboole_0(k2_relat_1(A_16)) | ~v1_relat_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.52  tff(c_492, plain, (![A_108]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_108, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_108, k1_xboole_0)) | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_474, c_26])).
% 2.69/1.52  tff(c_742, plain, (![A_117]: (~v1_relat_1(k5_relat_1(A_117, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_117, k1_xboole_0)) | ~v1_relat_1(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_492])).
% 2.69/1.52  tff(c_756, plain, (![A_118]: (k5_relat_1(A_118, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_118, k1_xboole_0)) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_742, c_8])).
% 2.69/1.52  tff(c_763, plain, (![A_13]: (k5_relat_1(A_13, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_22, c_756])).
% 2.69/1.52  tff(c_769, plain, (![A_119]: (k5_relat_1(A_119, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_763])).
% 2.69/1.52  tff(c_778, plain, (k5_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_769])).
% 2.69/1.52  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_288, c_778])).
% 2.69/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.52  
% 2.69/1.52  Inference rules
% 2.69/1.52  ----------------------
% 2.69/1.52  #Ref     : 0
% 2.69/1.52  #Sup     : 157
% 2.69/1.52  #Fact    : 0
% 2.69/1.52  #Define  : 0
% 2.69/1.52  #Split   : 2
% 2.69/1.52  #Chain   : 0
% 2.69/1.52  #Close   : 0
% 2.69/1.52  
% 2.69/1.52  Ordering : KBO
% 2.69/1.52  
% 2.69/1.52  Simplification rules
% 2.69/1.52  ----------------------
% 2.69/1.52  #Subsume      : 9
% 2.69/1.52  #Demod        : 147
% 2.69/1.52  #Tautology    : 93
% 2.69/1.52  #SimpNegUnit  : 2
% 2.69/1.52  #BackRed      : 4
% 2.69/1.52  
% 2.69/1.52  #Partial instantiations: 0
% 2.69/1.52  #Strategies tried      : 1
% 2.69/1.52  
% 2.69/1.52  Timing (in seconds)
% 2.69/1.52  ----------------------
% 2.69/1.52  Preprocessing        : 0.33
% 2.69/1.53  Parsing              : 0.18
% 2.69/1.53  CNF conversion       : 0.02
% 2.69/1.53  Main loop            : 0.33
% 2.69/1.53  Inferencing          : 0.14
% 2.69/1.53  Reduction            : 0.09
% 2.69/1.53  Demodulation         : 0.06
% 2.69/1.53  BG Simplification    : 0.02
% 2.69/1.53  Subsumption          : 0.06
% 2.69/1.53  Abstraction          : 0.01
% 2.69/1.53  MUC search           : 0.00
% 2.69/1.53  Cooper               : 0.00
% 2.69/1.53  Total                : 0.70
% 2.69/1.53  Index Insertion      : 0.00
% 2.69/1.53  Index Deletion       : 0.00
% 2.69/1.53  Index Matching       : 0.00
% 2.69/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
