%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:00 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   56 (  90 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 146 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [B_29,A_30] : k1_setfam_1(k2_tarski(B_29,A_30)) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_160,plain,(
    ! [C_38,A_39,B_40] :
      ( k7_relat_1(k7_relat_1(C_38,A_39),B_40) = k7_relat_1(C_38,k3_xboole_0(A_39,B_40))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(k7_relat_1(B_18,A_17)) = k9_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_185,plain,(
    ! [C_44,A_45,B_46] :
      ( k2_relat_1(k7_relat_1(C_44,k3_xboole_0(A_45,B_46))) = k9_relat_1(k7_relat_1(C_44,A_45),B_46)
      | ~ v1_relat_1(k7_relat_1(C_44,A_45))
      | ~ v1_relat_1(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_16])).

tff(c_415,plain,(
    ! [C_69,A_70,B_71] :
      ( k9_relat_1(k7_relat_1(C_69,A_70),B_71) = k9_relat_1(C_69,k3_xboole_0(A_70,B_71))
      | ~ v1_relat_1(C_69)
      | ~ v1_relat_1(k7_relat_1(C_69,A_70))
      | ~ v1_relat_1(C_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_16])).

tff(c_421,plain,(
    ! [A_72,B_73,B_74] :
      ( k9_relat_1(k7_relat_1(A_72,B_73),B_74) = k9_relat_1(A_72,k3_xboole_0(B_73,B_74))
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_10,c_415])).

tff(c_137,plain,(
    ! [B_33,A_34] :
      ( k2_relat_1(k7_relat_1(B_33,A_34)) = k9_relat_1(B_33,A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,A_15),k2_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_143,plain,(
    ! [B_33,A_34,A_15] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_33,A_34),A_15),k9_relat_1(B_33,A_34))
      | ~ v1_relat_1(k7_relat_1(B_33,A_34))
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_14])).

tff(c_551,plain,(
    ! [A_85,B_86,B_87] :
      ( r1_tarski(k9_relat_1(A_85,k3_xboole_0(B_86,B_87)),k9_relat_1(A_85,B_86))
      | ~ v1_relat_1(k7_relat_1(A_85,B_86))
      | ~ v1_relat_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_143])).

tff(c_565,plain,(
    ! [A_88,B_89,A_90] :
      ( r1_tarski(k9_relat_1(A_88,k3_xboole_0(B_89,A_90)),k9_relat_1(A_88,A_90))
      | ~ v1_relat_1(k7_relat_1(A_88,A_90))
      | ~ v1_relat_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_551])).

tff(c_250,plain,(
    ! [C_50,A_51,B_52] :
      ( k9_relat_1(k7_relat_1(C_50,A_51),B_52) = k9_relat_1(C_50,k3_xboole_0(A_51,B_52))
      | ~ v1_relat_1(C_50)
      | ~ v1_relat_1(k7_relat_1(C_50,A_51))
      | ~ v1_relat_1(C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_16])).

tff(c_256,plain,(
    ! [A_53,B_54,B_55] :
      ( k9_relat_1(k7_relat_1(A_53,B_54),B_55) = k9_relat_1(A_53,k3_xboole_0(B_54,B_55))
      | ~ v1_relat_1(A_53) ) ),
    inference(resolution,[status(thm)],[c_10,c_250])).

tff(c_386,plain,(
    ! [A_66,B_67,B_68] :
      ( r1_tarski(k9_relat_1(A_66,k3_xboole_0(B_67,B_68)),k9_relat_1(A_66,B_67))
      | ~ v1_relat_1(k7_relat_1(A_66,B_67))
      | ~ v1_relat_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_143])).

tff(c_149,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_tarski(A_35,k3_xboole_0(B_36,C_37))
      | ~ r1_tarski(A_35,C_37)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_159,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_149,c_18])).

tff(c_249,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_389,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_386,c_249])).

tff(c_405,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_389])).

tff(c_408,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_405])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_408])).

tff(c_413,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_568,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_565,c_413])).

tff(c_584,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_568])).

tff(c_587,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_584])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.46  
% 2.76/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.46  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.76/1.46  
% 2.76/1.46  %Foreground sorts:
% 2.76/1.46  
% 2.76/1.46  
% 2.76/1.46  %Background operators:
% 2.76/1.46  
% 2.76/1.46  
% 2.76/1.46  %Foreground operators:
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.76/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.76/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.76/1.46  
% 2.76/1.48  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 2.76/1.48  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.76/1.48  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.76/1.48  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.76/1.48  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.76/1.48  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.76/1.48  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 2.76/1.48  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.76/1.48  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.48  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.48  tff(c_4, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.48  tff(c_64, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.48  tff(c_80, plain, (![B_29, A_30]: (k1_setfam_1(k2_tarski(B_29, A_30))=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_4, c_64])).
% 2.76/1.48  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.48  tff(c_86, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 2.76/1.48  tff(c_160, plain, (![C_38, A_39, B_40]: (k7_relat_1(k7_relat_1(C_38, A_39), B_40)=k7_relat_1(C_38, k3_xboole_0(A_39, B_40)) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.48  tff(c_16, plain, (![B_18, A_17]: (k2_relat_1(k7_relat_1(B_18, A_17))=k9_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.48  tff(c_185, plain, (![C_44, A_45, B_46]: (k2_relat_1(k7_relat_1(C_44, k3_xboole_0(A_45, B_46)))=k9_relat_1(k7_relat_1(C_44, A_45), B_46) | ~v1_relat_1(k7_relat_1(C_44, A_45)) | ~v1_relat_1(C_44))), inference(superposition, [status(thm), theory('equality')], [c_160, c_16])).
% 2.76/1.48  tff(c_415, plain, (![C_69, A_70, B_71]: (k9_relat_1(k7_relat_1(C_69, A_70), B_71)=k9_relat_1(C_69, k3_xboole_0(A_70, B_71)) | ~v1_relat_1(C_69) | ~v1_relat_1(k7_relat_1(C_69, A_70)) | ~v1_relat_1(C_69))), inference(superposition, [status(thm), theory('equality')], [c_185, c_16])).
% 2.76/1.48  tff(c_421, plain, (![A_72, B_73, B_74]: (k9_relat_1(k7_relat_1(A_72, B_73), B_74)=k9_relat_1(A_72, k3_xboole_0(B_73, B_74)) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_10, c_415])).
% 2.76/1.48  tff(c_137, plain, (![B_33, A_34]: (k2_relat_1(k7_relat_1(B_33, A_34))=k9_relat_1(B_33, A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.48  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, A_15), k2_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.76/1.48  tff(c_143, plain, (![B_33, A_34, A_15]: (r1_tarski(k9_relat_1(k7_relat_1(B_33, A_34), A_15), k9_relat_1(B_33, A_34)) | ~v1_relat_1(k7_relat_1(B_33, A_34)) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_137, c_14])).
% 2.76/1.48  tff(c_551, plain, (![A_85, B_86, B_87]: (r1_tarski(k9_relat_1(A_85, k3_xboole_0(B_86, B_87)), k9_relat_1(A_85, B_86)) | ~v1_relat_1(k7_relat_1(A_85, B_86)) | ~v1_relat_1(A_85) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_421, c_143])).
% 2.76/1.48  tff(c_565, plain, (![A_88, B_89, A_90]: (r1_tarski(k9_relat_1(A_88, k3_xboole_0(B_89, A_90)), k9_relat_1(A_88, A_90)) | ~v1_relat_1(k7_relat_1(A_88, A_90)) | ~v1_relat_1(A_88) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_86, c_551])).
% 2.76/1.48  tff(c_250, plain, (![C_50, A_51, B_52]: (k9_relat_1(k7_relat_1(C_50, A_51), B_52)=k9_relat_1(C_50, k3_xboole_0(A_51, B_52)) | ~v1_relat_1(C_50) | ~v1_relat_1(k7_relat_1(C_50, A_51)) | ~v1_relat_1(C_50))), inference(superposition, [status(thm), theory('equality')], [c_185, c_16])).
% 2.76/1.48  tff(c_256, plain, (![A_53, B_54, B_55]: (k9_relat_1(k7_relat_1(A_53, B_54), B_55)=k9_relat_1(A_53, k3_xboole_0(B_54, B_55)) | ~v1_relat_1(A_53))), inference(resolution, [status(thm)], [c_10, c_250])).
% 2.76/1.48  tff(c_386, plain, (![A_66, B_67, B_68]: (r1_tarski(k9_relat_1(A_66, k3_xboole_0(B_67, B_68)), k9_relat_1(A_66, B_67)) | ~v1_relat_1(k7_relat_1(A_66, B_67)) | ~v1_relat_1(A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_256, c_143])).
% 2.76/1.48  tff(c_149, plain, (![A_35, B_36, C_37]: (r1_tarski(A_35, k3_xboole_0(B_36, C_37)) | ~r1_tarski(A_35, C_37) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.48  tff(c_18, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.48  tff(c_159, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_149, c_18])).
% 2.76/1.48  tff(c_249, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_159])).
% 2.76/1.48  tff(c_389, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_386, c_249])).
% 2.76/1.48  tff(c_405, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_389])).
% 2.76/1.48  tff(c_408, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_405])).
% 2.76/1.48  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_408])).
% 2.76/1.48  tff(c_413, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_159])).
% 2.76/1.48  tff(c_568, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_565, c_413])).
% 2.76/1.48  tff(c_584, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_568])).
% 2.76/1.48  tff(c_587, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_584])).
% 2.76/1.48  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_587])).
% 2.76/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.48  
% 2.76/1.48  Inference rules
% 2.76/1.48  ----------------------
% 2.76/1.48  #Ref     : 0
% 2.76/1.48  #Sup     : 155
% 2.76/1.48  #Fact    : 0
% 2.76/1.48  #Define  : 0
% 2.76/1.48  #Split   : 1
% 2.76/1.48  #Chain   : 0
% 2.76/1.48  #Close   : 0
% 2.76/1.48  
% 2.76/1.48  Ordering : KBO
% 2.76/1.48  
% 2.76/1.48  Simplification rules
% 2.76/1.48  ----------------------
% 2.76/1.48  #Subsume      : 20
% 2.76/1.48  #Demod        : 7
% 2.76/1.48  #Tautology    : 41
% 2.76/1.48  #SimpNegUnit  : 0
% 2.76/1.48  #BackRed      : 0
% 2.76/1.48  
% 2.76/1.48  #Partial instantiations: 0
% 2.76/1.48  #Strategies tried      : 1
% 2.76/1.48  
% 2.76/1.48  Timing (in seconds)
% 2.76/1.48  ----------------------
% 2.76/1.48  Preprocessing        : 0.29
% 2.76/1.48  Parsing              : 0.16
% 2.76/1.48  CNF conversion       : 0.02
% 2.76/1.48  Main loop            : 0.35
% 2.76/1.48  Inferencing          : 0.14
% 2.76/1.48  Reduction            : 0.10
% 2.76/1.48  Demodulation         : 0.08
% 2.76/1.48  BG Simplification    : 0.02
% 2.76/1.48  Subsumption          : 0.06
% 2.76/1.48  Abstraction          : 0.02
% 2.76/1.48  MUC search           : 0.00
% 2.76/1.48  Cooper               : 0.00
% 2.76/1.48  Total                : 0.67
% 2.76/1.48  Index Insertion      : 0.00
% 2.76/1.48  Index Deletion       : 0.00
% 2.76/1.48  Index Matching       : 0.00
% 2.76/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
