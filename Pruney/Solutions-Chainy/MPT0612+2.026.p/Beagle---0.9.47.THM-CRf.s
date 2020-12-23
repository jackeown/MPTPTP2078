%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:44 EST 2020

% Result     : Theorem 15.47s
% Output     : CNFRefutation 15.47s
% Verified   : 
% Statistics : Number of formulae       :   47 (  54 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 (  80 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(C_14,k6_subset_1(A_12,B_13)) = k6_subset_1(C_14,k7_relat_1(C_14,B_13))
      | ~ r1_tarski(k1_relat_1(C_14),A_12)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_103,plain,(
    ! [C_47,A_48,B_49] :
      ( k7_relat_1(C_47,k4_xboole_0(A_48,B_49)) = k4_xboole_0(C_47,k7_relat_1(C_47,B_49))
      | ~ r1_tarski(k1_relat_1(C_47),A_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_14])).

tff(c_110,plain,(
    ! [C_47,B_2,B_49] :
      ( k7_relat_1(C_47,k4_xboole_0(k2_xboole_0(k1_relat_1(C_47),B_2),B_49)) = k4_xboole_0(C_47,k7_relat_1(C_47,B_49))
      | ~ v1_relat_1(C_47) ) ),
    inference(resolution,[status(thm)],[c_2,c_103])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_xboole_0(A_31,k4_xboole_0(C_32,B_33))
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [A_31,C_32,B_33] :
      ( k4_xboole_0(A_31,k4_xboole_0(C_32,B_33)) = A_31
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(resolution,[status(thm)],[c_47,c_4])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,k4_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    ! [B_39,A_40] :
      ( k7_relat_1(B_39,A_40) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_39),A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_142,plain,(
    ! [B_52,C_53,B_54] :
      ( k7_relat_1(B_52,k4_xboole_0(C_53,B_54)) = k1_xboole_0
      | ~ v1_relat_1(B_52)
      | ~ r1_tarski(k1_relat_1(B_52),B_54) ) ),
    inference(resolution,[status(thm)],[c_8,c_75])).

tff(c_5008,plain,(
    ! [B_250,A_251,C_252] :
      ( k7_relat_1(k7_relat_1(B_250,A_251),k4_xboole_0(C_252,A_251)) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(B_250,A_251))
      | ~ v1_relat_1(B_250) ) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_20220,plain,(
    ! [B_634,C_635,B_636,A_637] :
      ( k7_relat_1(k7_relat_1(B_634,k4_xboole_0(C_635,B_636)),A_637) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(B_634,k4_xboole_0(C_635,B_636)))
      | ~ v1_relat_1(B_634)
      | ~ r1_tarski(A_637,B_636) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_5008])).

tff(c_24875,plain,(
    ! [A_790,C_791,B_792,A_793] :
      ( k7_relat_1(k7_relat_1(A_790,k4_xboole_0(C_791,B_792)),A_793) = k1_xboole_0
      | ~ r1_tarski(A_793,B_792)
      | ~ v1_relat_1(A_790) ) ),
    inference(resolution,[status(thm)],[c_12,c_20220])).

tff(c_36964,plain,(
    ! [C_1028,B_1029,A_1030] :
      ( k7_relat_1(k4_xboole_0(C_1028,k7_relat_1(C_1028,B_1029)),A_1030) = k1_xboole_0
      | ~ r1_tarski(A_1030,B_1029)
      | ~ v1_relat_1(C_1028)
      | ~ v1_relat_1(C_1028) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_24875])).

tff(c_22,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_27,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_37435,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36964,c_27])).

tff(c_37708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_37435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:27:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.47/7.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.47/7.00  
% 15.47/7.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.47/7.01  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 15.47/7.01  
% 15.47/7.01  %Foreground sorts:
% 15.47/7.01  
% 15.47/7.01  
% 15.47/7.01  %Background operators:
% 15.47/7.01  
% 15.47/7.01  
% 15.47/7.01  %Foreground operators:
% 15.47/7.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.47/7.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.47/7.01  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.47/7.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.47/7.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.47/7.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.47/7.01  tff('#skF_2', type, '#skF_2': $i).
% 15.47/7.01  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 15.47/7.01  tff('#skF_3', type, '#skF_3': $i).
% 15.47/7.01  tff('#skF_1', type, '#skF_1': $i).
% 15.47/7.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.47/7.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.47/7.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.47/7.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.47/7.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.47/7.01  
% 15.47/7.02  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 15.47/7.02  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 15.47/7.02  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 15.47/7.02  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 15.47/7.02  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 15.47/7.02  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 15.47/7.02  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 15.47/7.02  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 15.47/7.02  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 15.47/7.02  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.47/7.02  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.47/7.02  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.47/7.02  tff(c_10, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.47/7.02  tff(c_14, plain, (![C_14, A_12, B_13]: (k7_relat_1(C_14, k6_subset_1(A_12, B_13))=k6_subset_1(C_14, k7_relat_1(C_14, B_13)) | ~r1_tarski(k1_relat_1(C_14), A_12) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.47/7.02  tff(c_103, plain, (![C_47, A_48, B_49]: (k7_relat_1(C_47, k4_xboole_0(A_48, B_49))=k4_xboole_0(C_47, k7_relat_1(C_47, B_49)) | ~r1_tarski(k1_relat_1(C_47), A_48) | ~v1_relat_1(C_47))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_14])).
% 15.47/7.02  tff(c_110, plain, (![C_47, B_2, B_49]: (k7_relat_1(C_47, k4_xboole_0(k2_xboole_0(k1_relat_1(C_47), B_2), B_49))=k4_xboole_0(C_47, k7_relat_1(C_47, B_49)) | ~v1_relat_1(C_47))), inference(resolution, [status(thm)], [c_2, c_103])).
% 15.47/7.02  tff(c_12, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.47/7.02  tff(c_47, plain, (![A_31, C_32, B_33]: (r1_xboole_0(A_31, k4_xboole_0(C_32, B_33)) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.47/7.02  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.47/7.02  tff(c_51, plain, (![A_31, C_32, B_33]: (k4_xboole_0(A_31, k4_xboole_0(C_32, B_33))=A_31 | ~r1_tarski(A_31, B_33))), inference(resolution, [status(thm)], [c_47, c_4])).
% 15.47/7.02  tff(c_16, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.47/7.02  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, k4_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.47/7.02  tff(c_75, plain, (![B_39, A_40]: (k7_relat_1(B_39, A_40)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_39), A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.47/7.02  tff(c_142, plain, (![B_52, C_53, B_54]: (k7_relat_1(B_52, k4_xboole_0(C_53, B_54))=k1_xboole_0 | ~v1_relat_1(B_52) | ~r1_tarski(k1_relat_1(B_52), B_54))), inference(resolution, [status(thm)], [c_8, c_75])).
% 15.47/7.02  tff(c_5008, plain, (![B_250, A_251, C_252]: (k7_relat_1(k7_relat_1(B_250, A_251), k4_xboole_0(C_252, A_251))=k1_xboole_0 | ~v1_relat_1(k7_relat_1(B_250, A_251)) | ~v1_relat_1(B_250))), inference(resolution, [status(thm)], [c_16, c_142])).
% 15.47/7.02  tff(c_20220, plain, (![B_634, C_635, B_636, A_637]: (k7_relat_1(k7_relat_1(B_634, k4_xboole_0(C_635, B_636)), A_637)=k1_xboole_0 | ~v1_relat_1(k7_relat_1(B_634, k4_xboole_0(C_635, B_636))) | ~v1_relat_1(B_634) | ~r1_tarski(A_637, B_636))), inference(superposition, [status(thm), theory('equality')], [c_51, c_5008])).
% 15.47/7.02  tff(c_24875, plain, (![A_790, C_791, B_792, A_793]: (k7_relat_1(k7_relat_1(A_790, k4_xboole_0(C_791, B_792)), A_793)=k1_xboole_0 | ~r1_tarski(A_793, B_792) | ~v1_relat_1(A_790))), inference(resolution, [status(thm)], [c_12, c_20220])).
% 15.47/7.02  tff(c_36964, plain, (![C_1028, B_1029, A_1030]: (k7_relat_1(k4_xboole_0(C_1028, k7_relat_1(C_1028, B_1029)), A_1030)=k1_xboole_0 | ~r1_tarski(A_1030, B_1029) | ~v1_relat_1(C_1028) | ~v1_relat_1(C_1028))), inference(superposition, [status(thm), theory('equality')], [c_110, c_24875])).
% 15.47/7.02  tff(c_22, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.47/7.02  tff(c_27, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 15.47/7.02  tff(c_37435, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36964, c_27])).
% 15.47/7.02  tff(c_37708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_37435])).
% 15.47/7.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.47/7.02  
% 15.47/7.02  Inference rules
% 15.47/7.02  ----------------------
% 15.47/7.02  #Ref     : 0
% 15.47/7.02  #Sup     : 9766
% 15.47/7.02  #Fact    : 0
% 15.47/7.02  #Define  : 0
% 15.47/7.02  #Split   : 42
% 15.47/7.02  #Chain   : 0
% 15.47/7.02  #Close   : 0
% 15.47/7.02  
% 15.47/7.02  Ordering : KBO
% 15.47/7.02  
% 15.47/7.02  Simplification rules
% 15.47/7.02  ----------------------
% 15.47/7.02  #Subsume      : 1682
% 15.47/7.02  #Demod        : 7432
% 15.47/7.02  #Tautology    : 2662
% 15.47/7.02  #SimpNegUnit  : 16
% 15.47/7.02  #BackRed      : 26
% 15.47/7.02  
% 15.47/7.02  #Partial instantiations: 0
% 15.47/7.02  #Strategies tried      : 1
% 15.47/7.02  
% 15.47/7.02  Timing (in seconds)
% 15.47/7.02  ----------------------
% 15.47/7.02  Preprocessing        : 0.29
% 15.47/7.02  Parsing              : 0.16
% 15.47/7.02  CNF conversion       : 0.02
% 15.47/7.02  Main loop            : 5.97
% 15.47/7.02  Inferencing          : 1.70
% 15.47/7.02  Reduction            : 1.78
% 15.47/7.02  Demodulation         : 1.32
% 15.47/7.02  BG Simplification    : 0.28
% 15.47/7.02  Subsumption          : 1.84
% 15.47/7.02  Abstraction          : 0.36
% 15.47/7.02  MUC search           : 0.00
% 15.47/7.02  Cooper               : 0.00
% 15.47/7.02  Total                : 6.29
% 15.47/7.02  Index Insertion      : 0.00
% 15.47/7.02  Index Deletion       : 0.00
% 15.47/7.02  Index Matching       : 0.00
% 15.47/7.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
