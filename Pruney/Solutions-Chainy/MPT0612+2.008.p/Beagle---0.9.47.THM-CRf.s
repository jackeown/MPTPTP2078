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
% DateTime   : Thu Dec  3 10:02:42 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   53 (  61 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 (  79 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k4_xboole_0(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,k4_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_159,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),k3_xboole_0(A_42,B_43))
      | r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    ! [B_29,A_30] : k1_setfam_1(k2_tarski(B_29,A_30)) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_12,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_12])).

tff(c_144,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_150,plain,(
    ! [B_29,A_30,C_35] :
      ( ~ r1_xboole_0(B_29,A_30)
      | ~ r2_hidden(C_35,k3_xboole_0(A_30,B_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_144])).

tff(c_174,plain,(
    ! [B_44,A_45] :
      ( ~ r1_xboole_0(B_44,A_45)
      | r1_xboole_0(A_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_159,c_150])).

tff(c_177,plain,(
    ! [C_8,B_7,A_6] :
      ( r1_xboole_0(k4_xboole_0(C_8,B_7),A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_174])).

tff(c_10,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k6_subset_1(B_18,k7_relat_1(B_18,A_17))) = k6_subset_1(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_220,plain,(
    ! [B_57,A_58] :
      ( k1_relat_1(k4_xboole_0(B_57,k7_relat_1(B_57,A_58))) = k4_xboole_0(k1_relat_1(B_57),A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_245,plain,(
    ! [B_67,A_68,A_69] :
      ( k7_relat_1(k4_xboole_0(B_67,k7_relat_1(B_67,A_68)),A_69) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(B_67),A_68),A_69)
      | ~ v1_relat_1(k4_xboole_0(B_67,k7_relat_1(B_67,A_68)))
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_18])).

tff(c_260,plain,(
    ! [B_70,B_71,A_72] :
      ( k7_relat_1(k4_xboole_0(B_70,k7_relat_1(B_70,B_71)),A_72) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(B_70,k7_relat_1(B_70,B_71)))
      | ~ v1_relat_1(B_70)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_177,c_245])).

tff(c_265,plain,(
    ! [A_73,B_74,A_75] :
      ( k7_relat_1(k4_xboole_0(A_73,k7_relat_1(A_73,B_74)),A_75) = k1_xboole_0
      | ~ r1_tarski(A_75,B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_14,c_260])).

tff(c_22,plain,(
    k7_relat_1(k6_subset_1('#skF_4',k7_relat_1('#skF_4','#skF_3')),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    k7_relat_1(k4_xboole_0('#skF_4',k7_relat_1('#skF_4','#skF_3')),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_284,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_28])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.63  
% 2.63/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.63/1.64  
% 2.63/1.64  %Foreground sorts:
% 2.63/1.64  
% 2.63/1.64  
% 2.63/1.64  %Background operators:
% 2.63/1.64  
% 2.63/1.64  
% 2.63/1.64  %Foreground operators:
% 2.63/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.63/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.64  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.64  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.63/1.64  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.64  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.63/1.64  
% 2.63/1.66  tff(f_70, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 2.63/1.66  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.63/1.66  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.63/1.66  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.63/1.66  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.63/1.66  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.63/1.66  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.63/1.66  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 2.63/1.66  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.63/1.66  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.63/1.66  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.63/1.66  tff(c_14, plain, (![A_15, B_16]: (v1_relat_1(k4_xboole_0(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.63/1.66  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, k4_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.63/1.66  tff(c_159, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), k3_xboole_0(A_42, B_43)) | r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.63/1.66  tff(c_8, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.66  tff(c_72, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.66  tff(c_87, plain, (![B_29, A_30]: (k1_setfam_1(k2_tarski(B_29, A_30))=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_8, c_72])).
% 2.63/1.66  tff(c_12, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.66  tff(c_93, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_87, c_12])).
% 2.63/1.66  tff(c_144, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.63/1.66  tff(c_150, plain, (![B_29, A_30, C_35]: (~r1_xboole_0(B_29, A_30) | ~r2_hidden(C_35, k3_xboole_0(A_30, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_144])).
% 2.63/1.66  tff(c_174, plain, (![B_44, A_45]: (~r1_xboole_0(B_44, A_45) | r1_xboole_0(A_45, B_44))), inference(resolution, [status(thm)], [c_159, c_150])).
% 2.63/1.66  tff(c_177, plain, (![C_8, B_7, A_6]: (r1_xboole_0(k4_xboole_0(C_8, B_7), A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_6, c_174])).
% 2.63/1.66  tff(c_10, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.63/1.66  tff(c_16, plain, (![B_18, A_17]: (k1_relat_1(k6_subset_1(B_18, k7_relat_1(B_18, A_17)))=k6_subset_1(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.66  tff(c_220, plain, (![B_57, A_58]: (k1_relat_1(k4_xboole_0(B_57, k7_relat_1(B_57, A_58)))=k4_xboole_0(k1_relat_1(B_57), A_58) | ~v1_relat_1(B_57))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16])).
% 2.63/1.66  tff(c_18, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.63/1.66  tff(c_245, plain, (![B_67, A_68, A_69]: (k7_relat_1(k4_xboole_0(B_67, k7_relat_1(B_67, A_68)), A_69)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(B_67), A_68), A_69) | ~v1_relat_1(k4_xboole_0(B_67, k7_relat_1(B_67, A_68))) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_220, c_18])).
% 2.63/1.66  tff(c_260, plain, (![B_70, B_71, A_72]: (k7_relat_1(k4_xboole_0(B_70, k7_relat_1(B_70, B_71)), A_72)=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(B_70, k7_relat_1(B_70, B_71))) | ~v1_relat_1(B_70) | ~r1_tarski(A_72, B_71))), inference(resolution, [status(thm)], [c_177, c_245])).
% 2.63/1.66  tff(c_265, plain, (![A_73, B_74, A_75]: (k7_relat_1(k4_xboole_0(A_73, k7_relat_1(A_73, B_74)), A_75)=k1_xboole_0 | ~r1_tarski(A_75, B_74) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_14, c_260])).
% 2.63/1.66  tff(c_22, plain, (k7_relat_1(k6_subset_1('#skF_4', k7_relat_1('#skF_4', '#skF_3')), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.63/1.66  tff(c_28, plain, (k7_relat_1(k4_xboole_0('#skF_4', k7_relat_1('#skF_4', '#skF_3')), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 2.63/1.66  tff(c_284, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_265, c_28])).
% 2.63/1.66  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_284])).
% 2.63/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.66  
% 2.63/1.66  Inference rules
% 2.63/1.66  ----------------------
% 2.63/1.66  #Ref     : 0
% 2.63/1.66  #Sup     : 68
% 2.63/1.66  #Fact    : 0
% 2.63/1.66  #Define  : 0
% 2.63/1.66  #Split   : 0
% 2.63/1.66  #Chain   : 0
% 2.63/1.66  #Close   : 0
% 2.63/1.66  
% 2.63/1.66  Ordering : KBO
% 2.63/1.66  
% 2.63/1.66  Simplification rules
% 2.63/1.66  ----------------------
% 2.63/1.66  #Subsume      : 12
% 2.63/1.66  #Demod        : 8
% 2.63/1.66  #Tautology    : 31
% 2.63/1.66  #SimpNegUnit  : 0
% 2.63/1.66  #BackRed      : 0
% 2.63/1.66  
% 2.63/1.66  #Partial instantiations: 0
% 2.63/1.66  #Strategies tried      : 1
% 2.63/1.66  
% 2.63/1.66  Timing (in seconds)
% 2.63/1.66  ----------------------
% 2.63/1.67  Preprocessing        : 0.49
% 2.63/1.67  Parsing              : 0.26
% 2.63/1.67  CNF conversion       : 0.03
% 2.63/1.67  Main loop            : 0.34
% 2.63/1.67  Inferencing          : 0.13
% 2.63/1.67  Reduction            : 0.10
% 2.63/1.67  Demodulation         : 0.08
% 2.63/1.67  BG Simplification    : 0.02
% 2.63/1.67  Subsumption          : 0.06
% 2.63/1.67  Abstraction          : 0.02
% 2.63/1.67  MUC search           : 0.00
% 2.63/1.67  Cooper               : 0.00
% 2.63/1.67  Total                : 0.88
% 2.63/1.67  Index Insertion      : 0.00
% 2.63/1.67  Index Deletion       : 0.00
% 2.63/1.67  Index Matching       : 0.00
% 2.63/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
