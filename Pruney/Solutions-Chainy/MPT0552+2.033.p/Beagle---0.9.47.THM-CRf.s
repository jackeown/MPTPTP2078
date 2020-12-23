%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:01 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   49 (  81 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 140 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_71,plain,(
    ! [C_26,A_27,B_28] :
      ( k7_relat_1(k7_relat_1(C_26,A_27),B_28) = k7_relat_1(C_26,k3_xboole_0(A_27,B_28))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_332,plain,(
    ! [C_57,A_58,B_59] :
      ( k2_relat_1(k7_relat_1(C_57,k3_xboole_0(A_58,B_59))) = k9_relat_1(k7_relat_1(C_57,A_58),B_59)
      | ~ v1_relat_1(k7_relat_1(C_57,A_58))
      | ~ v1_relat_1(C_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_12])).

tff(c_450,plain,(
    ! [B_67,A_68,B_69] :
      ( k9_relat_1(k7_relat_1(B_67,A_68),B_69) = k9_relat_1(B_67,k3_xboole_0(A_68,B_69))
      | ~ v1_relat_1(k7_relat_1(B_67,A_68))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_332])).

tff(c_458,plain,(
    ! [A_70,B_71,B_72] :
      ( k9_relat_1(k7_relat_1(A_70,B_71),B_72) = k9_relat_1(A_70,k3_xboole_0(B_71,B_72))
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_450])).

tff(c_52,plain,(
    ! [B_21,A_22] :
      ( k2_relat_1(k7_relat_1(B_21,A_22)) = k9_relat_1(B_21,A_22)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k9_relat_1(B_12,A_11),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [B_21,A_22,A_11] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_21,A_22),A_11),k9_relat_1(B_21,A_22))
      | ~ v1_relat_1(k7_relat_1(B_21,A_22))
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_534,plain,(
    ! [A_79,B_80,B_81] :
      ( r1_tarski(k9_relat_1(A_79,k3_xboole_0(B_80,B_81)),k9_relat_1(A_79,B_80))
      | ~ v1_relat_1(k7_relat_1(A_79,B_80))
      | ~ v1_relat_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_58])).

tff(c_548,plain,(
    ! [A_82,B_83,A_84] :
      ( r1_tarski(k9_relat_1(A_82,k3_xboole_0(B_83,A_84)),k9_relat_1(A_82,A_84))
      | ~ v1_relat_1(k7_relat_1(A_82,A_84))
      | ~ v1_relat_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_534])).

tff(c_101,plain,(
    ! [C_32,A_33,B_34] :
      ( k2_relat_1(k7_relat_1(C_32,k3_xboole_0(A_33,B_34))) = k9_relat_1(k7_relat_1(C_32,A_33),B_34)
      | ~ v1_relat_1(k7_relat_1(C_32,A_33))
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_12])).

tff(c_165,plain,(
    ! [C_38,A_39,B_40] :
      ( k9_relat_1(k7_relat_1(C_38,A_39),B_40) = k9_relat_1(C_38,k3_xboole_0(A_39,B_40))
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(k7_relat_1(C_38,A_39))
      | ~ v1_relat_1(C_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_12])).

tff(c_227,plain,(
    ! [A_45,B_46,B_47] :
      ( k9_relat_1(k7_relat_1(A_45,B_46),B_47) = k9_relat_1(A_45,k3_xboole_0(B_46,B_47))
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_165])).

tff(c_303,plain,(
    ! [A_54,B_55,B_56] :
      ( r1_tarski(k9_relat_1(A_54,k3_xboole_0(B_55,B_56)),k9_relat_1(A_54,B_55))
      | ~ v1_relat_1(k7_relat_1(A_54,B_55))
      | ~ v1_relat_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_58])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,k3_xboole_0(B_4,C_5))
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_95,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_14])).

tff(c_100,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_306,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_303,c_100])).

tff(c_322,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_306])).

tff(c_325,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_322])).

tff(c_329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_325])).

tff(c_330,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_551,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_548,c_330])).

tff(c_567,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_551])).

tff(c_570,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_567])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:45:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.36  
% 2.42/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.36  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.42/1.36  
% 2.42/1.36  %Foreground sorts:
% 2.42/1.36  
% 2.42/1.36  
% 2.42/1.36  %Background operators:
% 2.42/1.36  
% 2.42/1.36  
% 2.42/1.36  %Foreground operators:
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.42/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.42/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.36  
% 2.66/1.38  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 2.66/1.38  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.66/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.66/1.38  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.66/1.38  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.66/1.38  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.66/1.38  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.66/1.38  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.66/1.38  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.66/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.38  tff(c_12, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.66/1.38  tff(c_71, plain, (![C_26, A_27, B_28]: (k7_relat_1(k7_relat_1(C_26, A_27), B_28)=k7_relat_1(C_26, k3_xboole_0(A_27, B_28)) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.66/1.38  tff(c_332, plain, (![C_57, A_58, B_59]: (k2_relat_1(k7_relat_1(C_57, k3_xboole_0(A_58, B_59)))=k9_relat_1(k7_relat_1(C_57, A_58), B_59) | ~v1_relat_1(k7_relat_1(C_57, A_58)) | ~v1_relat_1(C_57))), inference(superposition, [status(thm), theory('equality')], [c_71, c_12])).
% 2.66/1.38  tff(c_450, plain, (![B_67, A_68, B_69]: (k9_relat_1(k7_relat_1(B_67, A_68), B_69)=k9_relat_1(B_67, k3_xboole_0(A_68, B_69)) | ~v1_relat_1(k7_relat_1(B_67, A_68)) | ~v1_relat_1(B_67) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_12, c_332])).
% 2.66/1.38  tff(c_458, plain, (![A_70, B_71, B_72]: (k9_relat_1(k7_relat_1(A_70, B_71), B_72)=k9_relat_1(A_70, k3_xboole_0(B_71, B_72)) | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_6, c_450])).
% 2.66/1.38  tff(c_52, plain, (![B_21, A_22]: (k2_relat_1(k7_relat_1(B_21, A_22))=k9_relat_1(B_21, A_22) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.66/1.38  tff(c_10, plain, (![B_12, A_11]: (r1_tarski(k9_relat_1(B_12, A_11), k2_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.66/1.38  tff(c_58, plain, (![B_21, A_22, A_11]: (r1_tarski(k9_relat_1(k7_relat_1(B_21, A_22), A_11), k9_relat_1(B_21, A_22)) | ~v1_relat_1(k7_relat_1(B_21, A_22)) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_52, c_10])).
% 2.66/1.38  tff(c_534, plain, (![A_79, B_80, B_81]: (r1_tarski(k9_relat_1(A_79, k3_xboole_0(B_80, B_81)), k9_relat_1(A_79, B_80)) | ~v1_relat_1(k7_relat_1(A_79, B_80)) | ~v1_relat_1(A_79) | ~v1_relat_1(A_79))), inference(superposition, [status(thm), theory('equality')], [c_458, c_58])).
% 2.66/1.38  tff(c_548, plain, (![A_82, B_83, A_84]: (r1_tarski(k9_relat_1(A_82, k3_xboole_0(B_83, A_84)), k9_relat_1(A_82, A_84)) | ~v1_relat_1(k7_relat_1(A_82, A_84)) | ~v1_relat_1(A_82) | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_2, c_534])).
% 2.66/1.38  tff(c_101, plain, (![C_32, A_33, B_34]: (k2_relat_1(k7_relat_1(C_32, k3_xboole_0(A_33, B_34)))=k9_relat_1(k7_relat_1(C_32, A_33), B_34) | ~v1_relat_1(k7_relat_1(C_32, A_33)) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_71, c_12])).
% 2.66/1.38  tff(c_165, plain, (![C_38, A_39, B_40]: (k9_relat_1(k7_relat_1(C_38, A_39), B_40)=k9_relat_1(C_38, k3_xboole_0(A_39, B_40)) | ~v1_relat_1(C_38) | ~v1_relat_1(k7_relat_1(C_38, A_39)) | ~v1_relat_1(C_38))), inference(superposition, [status(thm), theory('equality')], [c_101, c_12])).
% 2.66/1.38  tff(c_227, plain, (![A_45, B_46, B_47]: (k9_relat_1(k7_relat_1(A_45, B_46), B_47)=k9_relat_1(A_45, k3_xboole_0(B_46, B_47)) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_6, c_165])).
% 2.66/1.38  tff(c_303, plain, (![A_54, B_55, B_56]: (r1_tarski(k9_relat_1(A_54, k3_xboole_0(B_55, B_56)), k9_relat_1(A_54, B_55)) | ~v1_relat_1(k7_relat_1(A_54, B_55)) | ~v1_relat_1(A_54) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_227, c_58])).
% 2.66/1.38  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, k3_xboole_0(B_4, C_5)) | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.66/1.38  tff(c_14, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.66/1.38  tff(c_95, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_14])).
% 2.66/1.38  tff(c_100, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_95])).
% 2.66/1.38  tff(c_306, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_303, c_100])).
% 2.66/1.38  tff(c_322, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_306])).
% 2.66/1.38  tff(c_325, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_322])).
% 2.66/1.38  tff(c_329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_325])).
% 2.66/1.38  tff(c_330, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_95])).
% 2.66/1.38  tff(c_551, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_548, c_330])).
% 2.66/1.38  tff(c_567, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_551])).
% 2.66/1.38  tff(c_570, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_567])).
% 2.66/1.38  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_570])).
% 2.66/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.38  
% 2.66/1.38  Inference rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Ref     : 0
% 2.66/1.38  #Sup     : 155
% 2.66/1.38  #Fact    : 0
% 2.66/1.38  #Define  : 0
% 2.66/1.38  #Split   : 1
% 2.66/1.38  #Chain   : 0
% 2.66/1.38  #Close   : 0
% 2.66/1.38  
% 2.66/1.38  Ordering : KBO
% 2.66/1.38  
% 2.66/1.38  Simplification rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Subsume      : 23
% 2.66/1.38  #Demod        : 4
% 2.66/1.38  #Tautology    : 28
% 2.66/1.38  #SimpNegUnit  : 0
% 2.66/1.38  #BackRed      : 0
% 2.66/1.38  
% 2.66/1.38  #Partial instantiations: 0
% 2.66/1.38  #Strategies tried      : 1
% 2.66/1.38  
% 2.66/1.38  Timing (in seconds)
% 2.66/1.38  ----------------------
% 2.66/1.38  Preprocessing        : 0.27
% 2.66/1.38  Parsing              : 0.15
% 2.66/1.38  CNF conversion       : 0.02
% 2.66/1.38  Main loop            : 0.36
% 2.66/1.38  Inferencing          : 0.14
% 2.66/1.38  Reduction            : 0.11
% 2.66/1.38  Demodulation         : 0.09
% 2.66/1.38  BG Simplification    : 0.02
% 2.66/1.38  Subsumption          : 0.07
% 2.66/1.38  Abstraction          : 0.02
% 2.66/1.38  MUC search           : 0.00
% 2.66/1.38  Cooper               : 0.00
% 2.66/1.38  Total                : 0.66
% 2.66/1.38  Index Insertion      : 0.00
% 2.66/1.38  Index Deletion       : 0.00
% 2.66/1.38  Index Matching       : 0.00
% 2.66/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
