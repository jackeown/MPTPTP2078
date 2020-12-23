%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:55 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 263 expanded)
%              Number of leaves         :   37 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 511 expanded)
%              Number of equality atoms :   68 ( 275 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_55,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_32,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_127,plain,(
    ! [A_41,B_42] :
      ( k9_relat_1(A_41,k1_tarski(B_42)) = k11_relat_1(A_41,B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_149,plain,(
    ! [A_48] :
      ( k9_relat_1(A_48,k1_relat_1('#skF_3')) = k11_relat_1(A_48,'#skF_2')
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_127])).

tff(c_26,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_156,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_26])).

tff(c_166,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_156])).

tff(c_20,plain,(
    ! [A_13] : k1_setfam_1(k1_tarski(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_105,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = k1_setfam_1(k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_96])).

tff(c_108,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_105])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_176,plain,(
    ! [B_51,A_52] :
      ( k9_relat_1(B_51,A_52) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_51),A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_192,plain,(
    ! [B_58,B_59] :
      ( k9_relat_1(B_58,B_59) = k1_xboole_0
      | ~ v1_relat_1(B_58)
      | k3_xboole_0(k1_relat_1(B_58),B_59) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_176])).

tff(c_197,plain,(
    ! [B_60] :
      ( k9_relat_1(B_60,k1_relat_1(B_60)) = k1_xboole_0
      | ~ v1_relat_1(B_60)
      | k1_relat_1(B_60) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_192])).

tff(c_136,plain,(
    ! [A_41] :
      ( k9_relat_1(A_41,k1_relat_1('#skF_3')) = k11_relat_1(A_41,'#skF_2')
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_127])).

tff(c_204,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_136])).

tff(c_220,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_166,c_204])).

tff(c_224,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_182,plain,(
    ! [B_53,A_54] :
      ( r1_xboole_0(k1_relat_1(B_53),A_54)
      | k9_relat_1(B_53,A_54) != k1_xboole_0
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_232,plain,(
    ! [B_62,A_63] :
      ( k3_xboole_0(k1_relat_1(B_62),A_63) = k1_xboole_0
      | k9_relat_1(B_62,A_63) != k1_xboole_0
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_182,c_2])).

tff(c_258,plain,(
    ! [B_67] :
      ( k1_relat_1(B_67) = k1_xboole_0
      | k9_relat_1(B_67,k1_relat_1(B_67)) != k1_xboole_0
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_108])).

tff(c_265,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_258])).

tff(c_271,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_166,c_265])).

tff(c_272,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_271])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_1'(A_10,B_11),A_10)
      | k1_xboole_0 = A_10
      | k1_tarski(B_11) = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ r2_hidden(B_23,k11_relat_1(C_24,A_22))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_285,plain,(
    ! [C_72,A_73,B_74] :
      ( k1_funct_1(C_72,A_73) = B_74
      | ~ r2_hidden(k4_tarski(A_73,B_74),C_72)
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_344,plain,(
    ! [C_81,A_82,B_83] :
      ( k1_funct_1(C_81,A_82) = B_83
      | ~ v1_funct_1(C_81)
      | ~ r2_hidden(B_83,k11_relat_1(C_81,A_82))
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_32,c_285])).

tff(c_355,plain,(
    ! [B_83] :
      ( k1_funct_1('#skF_3','#skF_2') = B_83
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_83,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_344])).

tff(c_360,plain,(
    ! [B_84] :
      ( k1_funct_1('#skF_3','#skF_2') = B_84
      | ~ r2_hidden(B_84,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_355])).

tff(c_368,plain,(
    ! [B_11] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_11) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_360])).

tff(c_373,plain,(
    ! [B_85] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_85) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_368])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( '#skF_1'(A_10,B_11) != B_11
      | k1_xboole_0 = A_10
      | k1_tarski(B_11) = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_381,plain,(
    ! [B_85] :
      ( k1_funct_1('#skF_3','#skF_2') != B_85
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_85)
      | k2_relat_1('#skF_3') = k1_tarski(B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_16])).

tff(c_389,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_381])).

tff(c_42,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_42])).

tff(c_394,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_14,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_14])).

tff(c_403,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_52])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.33  
% 2.32/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.34  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.32/1.34  
% 2.32/1.34  %Foreground sorts:
% 2.32/1.34  
% 2.32/1.34  
% 2.32/1.34  %Background operators:
% 2.32/1.34  
% 2.32/1.34  
% 2.32/1.34  %Foreground operators:
% 2.32/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.32/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.34  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.32/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.32/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.32/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.32/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.32/1.34  
% 2.53/1.35  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.53/1.35  tff(f_97, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.53/1.35  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.53/1.35  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.53/1.35  tff(f_55, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.53/1.35  tff(f_32, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.53/1.35  tff(f_57, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.53/1.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.53/1.35  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.53/1.35  tff(f_53, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.53/1.35  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.53/1.35  tff(f_88, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.53/1.35  tff(f_39, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.53/1.35  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.53/1.35  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.53/1.35  tff(c_44, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.53/1.35  tff(c_127, plain, (![A_41, B_42]: (k9_relat_1(A_41, k1_tarski(B_42))=k11_relat_1(A_41, B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.35  tff(c_149, plain, (![A_48]: (k9_relat_1(A_48, k1_relat_1('#skF_3'))=k11_relat_1(A_48, '#skF_2') | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_44, c_127])).
% 2.53/1.35  tff(c_26, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.53/1.35  tff(c_156, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_149, c_26])).
% 2.53/1.35  tff(c_166, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_156])).
% 2.53/1.35  tff(c_20, plain, (![A_13]: (k1_setfam_1(k1_tarski(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.35  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.35  tff(c_96, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.53/1.35  tff(c_105, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=k1_setfam_1(k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_96])).
% 2.53/1.35  tff(c_108, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_105])).
% 2.53/1.35  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.35  tff(c_176, plain, (![B_51, A_52]: (k9_relat_1(B_51, A_52)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_51), A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.53/1.35  tff(c_192, plain, (![B_58, B_59]: (k9_relat_1(B_58, B_59)=k1_xboole_0 | ~v1_relat_1(B_58) | k3_xboole_0(k1_relat_1(B_58), B_59)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_176])).
% 2.53/1.35  tff(c_197, plain, (![B_60]: (k9_relat_1(B_60, k1_relat_1(B_60))=k1_xboole_0 | ~v1_relat_1(B_60) | k1_relat_1(B_60)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_192])).
% 2.53/1.35  tff(c_136, plain, (![A_41]: (k9_relat_1(A_41, k1_relat_1('#skF_3'))=k11_relat_1(A_41, '#skF_2') | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_44, c_127])).
% 2.53/1.35  tff(c_204, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | k1_relat_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_197, c_136])).
% 2.53/1.35  tff(c_220, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_166, c_204])).
% 2.53/1.35  tff(c_224, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_220])).
% 2.53/1.35  tff(c_182, plain, (![B_53, A_54]: (r1_xboole_0(k1_relat_1(B_53), A_54) | k9_relat_1(B_53, A_54)!=k1_xboole_0 | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.53/1.35  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.35  tff(c_232, plain, (![B_62, A_63]: (k3_xboole_0(k1_relat_1(B_62), A_63)=k1_xboole_0 | k9_relat_1(B_62, A_63)!=k1_xboole_0 | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_182, c_2])).
% 2.53/1.35  tff(c_258, plain, (![B_67]: (k1_relat_1(B_67)=k1_xboole_0 | k9_relat_1(B_67, k1_relat_1(B_67))!=k1_xboole_0 | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_232, c_108])).
% 2.53/1.35  tff(c_265, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_136, c_258])).
% 2.53/1.35  tff(c_271, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_166, c_265])).
% 2.53/1.35  tff(c_272, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_224, c_271])).
% 2.53/1.35  tff(c_18, plain, (![A_10, B_11]: (r2_hidden('#skF_1'(A_10, B_11), A_10) | k1_xboole_0=A_10 | k1_tarski(B_11)=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.35  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.53/1.35  tff(c_32, plain, (![A_22, B_23, C_24]: (r2_hidden(k4_tarski(A_22, B_23), C_24) | ~r2_hidden(B_23, k11_relat_1(C_24, A_22)) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_285, plain, (![C_72, A_73, B_74]: (k1_funct_1(C_72, A_73)=B_74 | ~r2_hidden(k4_tarski(A_73, B_74), C_72) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.53/1.35  tff(c_344, plain, (![C_81, A_82, B_83]: (k1_funct_1(C_81, A_82)=B_83 | ~v1_funct_1(C_81) | ~r2_hidden(B_83, k11_relat_1(C_81, A_82)) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_32, c_285])).
% 2.53/1.35  tff(c_355, plain, (![B_83]: (k1_funct_1('#skF_3', '#skF_2')=B_83 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_83, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_344])).
% 2.53/1.35  tff(c_360, plain, (![B_84]: (k1_funct_1('#skF_3', '#skF_2')=B_84 | ~r2_hidden(B_84, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_355])).
% 2.53/1.35  tff(c_368, plain, (![B_11]: ('#skF_1'(k2_relat_1('#skF_3'), B_11)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_11))), inference(resolution, [status(thm)], [c_18, c_360])).
% 2.53/1.35  tff(c_373, plain, (![B_85]: ('#skF_1'(k2_relat_1('#skF_3'), B_85)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_85))), inference(negUnitSimplification, [status(thm)], [c_272, c_368])).
% 2.53/1.35  tff(c_16, plain, (![A_10, B_11]: ('#skF_1'(A_10, B_11)!=B_11 | k1_xboole_0=A_10 | k1_tarski(B_11)=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.35  tff(c_381, plain, (![B_85]: (k1_funct_1('#skF_3', '#skF_2')!=B_85 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_85) | k2_relat_1('#skF_3')=k1_tarski(B_85))), inference(superposition, [status(thm), theory('equality')], [c_373, c_16])).
% 2.53/1.35  tff(c_389, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_272, c_381])).
% 2.53/1.35  tff(c_42, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.53/1.35  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_389, c_42])).
% 2.53/1.35  tff(c_394, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_220])).
% 2.53/1.35  tff(c_14, plain, (![A_9]: (~v1_xboole_0(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.35  tff(c_52, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_14])).
% 2.53/1.35  tff(c_403, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_394, c_52])).
% 2.53/1.35  tff(c_407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_403])).
% 2.53/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.35  
% 2.53/1.35  Inference rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Ref     : 0
% 2.53/1.35  #Sup     : 75
% 2.53/1.35  #Fact    : 0
% 2.53/1.35  #Define  : 0
% 2.53/1.35  #Split   : 3
% 2.53/1.35  #Chain   : 0
% 2.53/1.35  #Close   : 0
% 2.53/1.35  
% 2.53/1.35  Ordering : KBO
% 2.53/1.35  
% 2.53/1.35  Simplification rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Subsume      : 5
% 2.53/1.35  #Demod        : 30
% 2.53/1.35  #Tautology    : 40
% 2.53/1.35  #SimpNegUnit  : 6
% 2.53/1.35  #BackRed      : 8
% 2.53/1.35  
% 2.53/1.35  #Partial instantiations: 0
% 2.53/1.35  #Strategies tried      : 1
% 2.53/1.35  
% 2.53/1.35  Timing (in seconds)
% 2.53/1.35  ----------------------
% 2.53/1.36  Preprocessing        : 0.34
% 2.53/1.36  Parsing              : 0.18
% 2.53/1.36  CNF conversion       : 0.02
% 2.53/1.36  Main loop            : 0.24
% 2.53/1.36  Inferencing          : 0.09
% 2.53/1.36  Reduction            : 0.07
% 2.53/1.36  Demodulation         : 0.05
% 2.53/1.36  BG Simplification    : 0.02
% 2.53/1.36  Subsumption          : 0.03
% 2.53/1.36  Abstraction          : 0.01
% 2.53/1.36  MUC search           : 0.00
% 2.53/1.36  Cooper               : 0.00
% 2.53/1.36  Total                : 0.61
% 2.53/1.36  Index Insertion      : 0.00
% 2.53/1.36  Index Deletion       : 0.00
% 2.53/1.36  Index Matching       : 0.00
% 2.53/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
