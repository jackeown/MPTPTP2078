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
% DateTime   : Thu Dec  3 10:00:42 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  65 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_66,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_81,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_50,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_50])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,(
    ! [A_41] :
      ( k9_relat_1(A_41,k1_relat_1(A_41)) = k2_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_118,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_109])).

tff(c_122,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_30,c_118])).

tff(c_194,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(k9_relat_1(B_59,A_60),k9_relat_1(B_59,k1_relat_1(B_59)))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_206,plain,(
    ! [A_60] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_60),k9_relat_1(k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_194])).

tff(c_211,plain,(
    ! [A_61] : r1_tarski(k9_relat_1(k1_xboole_0,A_61),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_122,c_206])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_3'(A_56),B_57)
      | ~ r1_tarski(A_56,B_57)
      | k1_xboole_0 = A_56 ) ),
    inference(resolution,[status(thm)],[c_12,c_155])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_80,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_91,plain,(
    ! [A_13,C_38] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_38,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_95,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_91])).

tff(c_174,plain,(
    ! [A_56] :
      ( ~ r1_tarski(A_56,k1_xboole_0)
      | k1_xboole_0 = A_56 ) ),
    inference(resolution,[status(thm)],[c_162,c_95])).

tff(c_221,plain,(
    ! [A_61] : k9_relat_1(k1_xboole_0,A_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_211,c_174])).

tff(c_36,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  
% 2.08/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.08/1.33  
% 2.08/1.33  %Foreground sorts:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Background operators:
% 2.08/1.33  
% 2.08/1.33  
% 2.08/1.33  %Foreground operators:
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.08/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.08/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.33  
% 2.08/1.35  tff(f_78, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.08/1.35  tff(f_66, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.08/1.35  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.08/1.35  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.08/1.35  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 2.08/1.35  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.08/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.08/1.35  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.08/1.35  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.08/1.35  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.08/1.35  tff(f_81, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.08/1.35  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.08/1.35  tff(c_50, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.08/1.35  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_50])).
% 2.08/1.35  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.08/1.35  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.08/1.35  tff(c_109, plain, (![A_41]: (k9_relat_1(A_41, k1_relat_1(A_41))=k2_relat_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.08/1.35  tff(c_118, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_109])).
% 2.08/1.35  tff(c_122, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_30, c_118])).
% 2.08/1.35  tff(c_194, plain, (![B_59, A_60]: (r1_tarski(k9_relat_1(B_59, A_60), k9_relat_1(B_59, k1_relat_1(B_59))) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.08/1.35  tff(c_206, plain, (![A_60]: (r1_tarski(k9_relat_1(k1_xboole_0, A_60), k9_relat_1(k1_xboole_0, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_194])).
% 2.08/1.35  tff(c_211, plain, (![A_61]: (r1_tarski(k9_relat_1(k1_xboole_0, A_61), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_122, c_206])).
% 2.08/1.35  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.35  tff(c_155, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.35  tff(c_162, plain, (![A_56, B_57]: (r2_hidden('#skF_3'(A_56), B_57) | ~r1_tarski(A_56, B_57) | k1_xboole_0=A_56)), inference(resolution, [status(thm)], [c_12, c_155])).
% 2.08/1.35  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.35  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.35  tff(c_80, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.35  tff(c_91, plain, (![A_13, C_38]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_80])).
% 2.08/1.35  tff(c_95, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_91])).
% 2.08/1.35  tff(c_174, plain, (![A_56]: (~r1_tarski(A_56, k1_xboole_0) | k1_xboole_0=A_56)), inference(resolution, [status(thm)], [c_162, c_95])).
% 2.08/1.35  tff(c_221, plain, (![A_61]: (k9_relat_1(k1_xboole_0, A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_211, c_174])).
% 2.08/1.35  tff(c_36, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.08/1.35  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_36])).
% 2.08/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.35  
% 2.08/1.35  Inference rules
% 2.08/1.35  ----------------------
% 2.08/1.35  #Ref     : 0
% 2.08/1.35  #Sup     : 43
% 2.08/1.35  #Fact    : 0
% 2.08/1.35  #Define  : 0
% 2.08/1.35  #Split   : 0
% 2.08/1.35  #Chain   : 0
% 2.08/1.35  #Close   : 0
% 2.08/1.35  
% 2.08/1.35  Ordering : KBO
% 2.08/1.35  
% 2.08/1.35  Simplification rules
% 2.08/1.35  ----------------------
% 2.08/1.35  #Subsume      : 1
% 2.08/1.35  #Demod        : 19
% 2.08/1.35  #Tautology    : 28
% 2.08/1.35  #SimpNegUnit  : 0
% 2.08/1.35  #BackRed      : 2
% 2.08/1.35  
% 2.08/1.35  #Partial instantiations: 0
% 2.08/1.35  #Strategies tried      : 1
% 2.08/1.35  
% 2.08/1.35  Timing (in seconds)
% 2.08/1.35  ----------------------
% 2.08/1.35  Preprocessing        : 0.34
% 2.08/1.35  Parsing              : 0.17
% 2.08/1.35  CNF conversion       : 0.02
% 2.08/1.35  Main loop            : 0.15
% 2.08/1.35  Inferencing          : 0.06
% 2.08/1.35  Reduction            : 0.05
% 2.08/1.35  Demodulation         : 0.03
% 2.08/1.35  BG Simplification    : 0.01
% 2.08/1.35  Subsumption          : 0.02
% 2.08/1.35  Abstraction          : 0.01
% 2.08/1.35  MUC search           : 0.00
% 2.08/1.35  Cooper               : 0.00
% 2.08/1.35  Total                : 0.52
% 2.08/1.35  Index Insertion      : 0.00
% 2.08/1.35  Index Deletion       : 0.00
% 2.08/1.35  Index Matching       : 0.00
% 2.08/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
