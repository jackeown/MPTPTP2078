%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:43 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 (  75 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,k4_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6,B_7] : k6_subset_1(A_6,B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(C_17,k6_subset_1(A_15,B_16)) = k6_subset_1(C_17,k7_relat_1(C_17,B_16))
      | ~ r1_tarski(k1_relat_1(C_17),A_15)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [C_32,A_33,B_34] :
      ( k7_relat_1(C_32,k4_xboole_0(A_33,B_34)) = k4_xboole_0(C_32,k7_relat_1(C_32,B_34))
      | ~ r1_tarski(k1_relat_1(C_32),A_33)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_18])).

tff(c_77,plain,(
    ! [C_32,B_34] :
      ( k7_relat_1(C_32,k4_xboole_0(k1_relat_1(C_32),B_34)) = k4_xboole_0(C_32,k7_relat_1(C_32,B_34))
      | ~ v1_relat_1(C_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,k6_subset_1(k1_relat_1(B_14),A_13))) = k6_subset_1(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    ! [B_30,A_31] :
      ( k1_relat_1(k7_relat_1(B_30,k4_xboole_0(k1_relat_1(B_30),A_31))) = k4_xboole_0(k1_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16])).

tff(c_14,plain,(
    ! [A_10,B_12] :
      ( k7_relat_1(A_10,B_12) = k1_xboole_0
      | ~ r1_xboole_0(B_12,k1_relat_1(A_10))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    ! [B_39,A_40,B_41] :
      ( k7_relat_1(k7_relat_1(B_39,k4_xboole_0(k1_relat_1(B_39),A_40)),B_41) = k1_xboole_0
      | ~ r1_xboole_0(B_41,k4_xboole_0(k1_relat_1(B_39),A_40))
      | ~ v1_relat_1(k7_relat_1(B_39,k4_xboole_0(k1_relat_1(B_39),A_40)))
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_14])).

tff(c_138,plain,(
    ! [A_46,A_47,B_48] :
      ( k7_relat_1(k7_relat_1(A_46,k4_xboole_0(k1_relat_1(A_46),A_47)),B_48) = k1_xboole_0
      | ~ r1_xboole_0(B_48,k4_xboole_0(k1_relat_1(A_46),A_47))
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_12,c_100])).

tff(c_283,plain,(
    ! [C_58,B_59,B_60] :
      ( k7_relat_1(k4_xboole_0(C_58,k7_relat_1(C_58,B_59)),B_60) = k1_xboole_0
      | ~ r1_xboole_0(B_60,k4_xboole_0(k1_relat_1(C_58),B_59))
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_138])).

tff(c_294,plain,(
    ! [C_61,B_62,A_63] :
      ( k7_relat_1(k4_xboole_0(C_61,k7_relat_1(C_61,B_62)),A_63) = k1_xboole_0
      | ~ v1_relat_1(C_61)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(resolution,[status(thm)],[c_8,c_283])).

tff(c_20,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_27,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_328,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_27])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.32  
% 2.45/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.32  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.32  
% 2.45/1.32  %Foreground sorts:
% 2.45/1.32  
% 2.45/1.32  
% 2.45/1.32  %Background operators:
% 2.45/1.32  
% 2.45/1.32  
% 2.45/1.32  %Foreground operators:
% 2.45/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.45/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.32  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.45/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.45/1.32  
% 2.45/1.33  tff(f_65, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 2.45/1.33  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.45/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.45/1.33  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.45/1.33  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 2.45/1.33  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.45/1.33  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_relat_1)).
% 2.45/1.33  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.45/1.33  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.45/1.33  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.45/1.33  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, k4_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.33  tff(c_10, plain, (![A_6, B_7]: (k6_subset_1(A_6, B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.33  tff(c_18, plain, (![C_17, A_15, B_16]: (k7_relat_1(C_17, k6_subset_1(A_15, B_16))=k6_subset_1(C_17, k7_relat_1(C_17, B_16)) | ~r1_tarski(k1_relat_1(C_17), A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.45/1.33  tff(c_71, plain, (![C_32, A_33, B_34]: (k7_relat_1(C_32, k4_xboole_0(A_33, B_34))=k4_xboole_0(C_32, k7_relat_1(C_32, B_34)) | ~r1_tarski(k1_relat_1(C_32), A_33) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_18])).
% 2.45/1.33  tff(c_77, plain, (![C_32, B_34]: (k7_relat_1(C_32, k4_xboole_0(k1_relat_1(C_32), B_34))=k4_xboole_0(C_32, k7_relat_1(C_32, B_34)) | ~v1_relat_1(C_32))), inference(resolution, [status(thm)], [c_6, c_71])).
% 2.45/1.33  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.33  tff(c_16, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, k6_subset_1(k1_relat_1(B_14), A_13)))=k6_subset_1(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.45/1.33  tff(c_53, plain, (![B_30, A_31]: (k1_relat_1(k7_relat_1(B_30, k4_xboole_0(k1_relat_1(B_30), A_31)))=k4_xboole_0(k1_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16])).
% 2.45/1.33  tff(c_14, plain, (![A_10, B_12]: (k7_relat_1(A_10, B_12)=k1_xboole_0 | ~r1_xboole_0(B_12, k1_relat_1(A_10)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.45/1.33  tff(c_100, plain, (![B_39, A_40, B_41]: (k7_relat_1(k7_relat_1(B_39, k4_xboole_0(k1_relat_1(B_39), A_40)), B_41)=k1_xboole_0 | ~r1_xboole_0(B_41, k4_xboole_0(k1_relat_1(B_39), A_40)) | ~v1_relat_1(k7_relat_1(B_39, k4_xboole_0(k1_relat_1(B_39), A_40))) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_53, c_14])).
% 2.45/1.33  tff(c_138, plain, (![A_46, A_47, B_48]: (k7_relat_1(k7_relat_1(A_46, k4_xboole_0(k1_relat_1(A_46), A_47)), B_48)=k1_xboole_0 | ~r1_xboole_0(B_48, k4_xboole_0(k1_relat_1(A_46), A_47)) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_12, c_100])).
% 2.45/1.33  tff(c_283, plain, (![C_58, B_59, B_60]: (k7_relat_1(k4_xboole_0(C_58, k7_relat_1(C_58, B_59)), B_60)=k1_xboole_0 | ~r1_xboole_0(B_60, k4_xboole_0(k1_relat_1(C_58), B_59)) | ~v1_relat_1(C_58) | ~v1_relat_1(C_58))), inference(superposition, [status(thm), theory('equality')], [c_77, c_138])).
% 2.45/1.33  tff(c_294, plain, (![C_61, B_62, A_63]: (k7_relat_1(k4_xboole_0(C_61, k7_relat_1(C_61, B_62)), A_63)=k1_xboole_0 | ~v1_relat_1(C_61) | ~r1_tarski(A_63, B_62))), inference(resolution, [status(thm)], [c_8, c_283])).
% 2.45/1.33  tff(c_20, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.45/1.33  tff(c_27, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 2.45/1.33  tff(c_328, plain, (~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_294, c_27])).
% 2.45/1.33  tff(c_352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_328])).
% 2.45/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.33  
% 2.45/1.33  Inference rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Ref     : 0
% 2.45/1.33  #Sup     : 89
% 2.45/1.33  #Fact    : 0
% 2.45/1.33  #Define  : 0
% 2.45/1.33  #Split   : 3
% 2.45/1.33  #Chain   : 0
% 2.45/1.33  #Close   : 0
% 2.45/1.33  
% 2.45/1.33  Ordering : KBO
% 2.45/1.33  
% 2.45/1.33  Simplification rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Subsume      : 17
% 2.45/1.33  #Demod        : 9
% 2.45/1.33  #Tautology    : 15
% 2.45/1.33  #SimpNegUnit  : 6
% 2.45/1.33  #BackRed      : 3
% 2.45/1.33  
% 2.45/1.33  #Partial instantiations: 0
% 2.45/1.33  #Strategies tried      : 1
% 2.45/1.33  
% 2.45/1.33  Timing (in seconds)
% 2.45/1.33  ----------------------
% 2.45/1.34  Preprocessing        : 0.30
% 2.45/1.34  Parsing              : 0.16
% 2.45/1.34  CNF conversion       : 0.02
% 2.45/1.34  Main loop            : 0.27
% 2.45/1.34  Inferencing          : 0.10
% 2.45/1.34  Reduction            : 0.08
% 2.45/1.34  Demodulation         : 0.05
% 2.45/1.34  BG Simplification    : 0.02
% 2.45/1.34  Subsumption          : 0.06
% 2.45/1.34  Abstraction          : 0.02
% 2.45/1.34  MUC search           : 0.00
% 2.45/1.34  Cooper               : 0.00
% 2.45/1.34  Total                : 0.60
% 2.45/1.34  Index Insertion      : 0.00
% 2.45/1.34  Index Deletion       : 0.00
% 2.45/1.34  Index Matching       : 0.00
% 2.45/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
