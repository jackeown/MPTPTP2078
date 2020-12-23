%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:08 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 110 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_25,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden('#skF_1'(A_25,B_26),B_26)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_25])).

tff(c_45,plain,(
    ! [B_33,A_34] :
      ( k7_relat_1(B_33,A_34) = B_33
      | ~ r1_tarski(k1_relat_1(B_33),A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_51,plain,(
    ! [B_35] :
      ( k7_relat_1(B_35,k1_relat_1(B_35)) = B_35
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_57,plain,(
    ! [B_35] :
      ( k9_relat_1(B_35,k1_relat_1(B_35)) = k2_relat_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_12])).

tff(c_50,plain,(
    ! [B_33] :
      ( k7_relat_1(B_33,k1_relat_1(B_33)) = B_33
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_98,plain,(
    ! [B_43,C_44,A_45] :
      ( k7_relat_1(k5_relat_1(B_43,C_44),A_45) = k5_relat_1(k7_relat_1(B_43,A_45),C_44)
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_118,plain,(
    ! [B_46,A_47,C_48] :
      ( k2_relat_1(k5_relat_1(k7_relat_1(B_46,A_47),C_48)) = k9_relat_1(k5_relat_1(B_46,C_48),A_47)
      | ~ v1_relat_1(k5_relat_1(B_46,C_48))
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_12])).

tff(c_192,plain,(
    ! [B_57,C_58] :
      ( k9_relat_1(k5_relat_1(B_57,C_58),k1_relat_1(B_57)) = k2_relat_1(k5_relat_1(B_57,C_58))
      | ~ v1_relat_1(k5_relat_1(B_57,C_58))
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_118])).

tff(c_14,plain,(
    ! [B_15,C_17,A_14] :
      ( k9_relat_1(k5_relat_1(B_15,C_17),A_14) = k9_relat_1(C_17,k9_relat_1(B_15,A_14))
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_211,plain,(
    ! [C_59,B_60] :
      ( k9_relat_1(C_59,k9_relat_1(B_60,k1_relat_1(B_60))) = k2_relat_1(k5_relat_1(B_60,C_59))
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k5_relat_1(B_60,C_59))
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_14])).

tff(c_235,plain,(
    ! [C_61,B_62] :
      ( k9_relat_1(C_61,k2_relat_1(B_62)) = k2_relat_1(k5_relat_1(B_62,C_61))
      | ~ v1_relat_1(C_61)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(k5_relat_1(B_62,C_61))
      | ~ v1_relat_1(C_61)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_211])).

tff(c_261,plain,(
    ! [B_67,A_68] :
      ( k9_relat_1(B_67,k2_relat_1(A_68)) = k2_relat_1(k5_relat_1(A_68,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_8,c_235])).

tff(c_18,plain,(
    k9_relat_1('#skF_3',k2_relat_1('#skF_2')) != k2_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_271,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_18])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.41  
% 2.23/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.41  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.41  
% 2.23/1.41  %Foreground sorts:
% 2.23/1.41  
% 2.23/1.41  
% 2.23/1.41  %Background operators:
% 2.23/1.41  
% 2.23/1.41  
% 2.23/1.41  %Foreground operators:
% 2.23/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.23/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.23/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.41  
% 2.23/1.42  tff(f_70, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.23/1.42  tff(f_38, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.23/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.23/1.42  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.23/1.42  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.23/1.42  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 2.23/1.42  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.23/1.42  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.42  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.42  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.23/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.42  tff(c_25, plain, (![A_25, B_26]: (~r2_hidden('#skF_1'(A_25, B_26), B_26) | r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.42  tff(c_30, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_25])).
% 2.23/1.42  tff(c_45, plain, (![B_33, A_34]: (k7_relat_1(B_33, A_34)=B_33 | ~r1_tarski(k1_relat_1(B_33), A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.42  tff(c_51, plain, (![B_35]: (k7_relat_1(B_35, k1_relat_1(B_35))=B_35 | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_30, c_45])).
% 2.23/1.42  tff(c_12, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.42  tff(c_57, plain, (![B_35]: (k9_relat_1(B_35, k1_relat_1(B_35))=k2_relat_1(B_35) | ~v1_relat_1(B_35) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_51, c_12])).
% 2.23/1.42  tff(c_50, plain, (![B_33]: (k7_relat_1(B_33, k1_relat_1(B_33))=B_33 | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_30, c_45])).
% 2.23/1.42  tff(c_98, plain, (![B_43, C_44, A_45]: (k7_relat_1(k5_relat_1(B_43, C_44), A_45)=k5_relat_1(k7_relat_1(B_43, A_45), C_44) | ~v1_relat_1(C_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.42  tff(c_118, plain, (![B_46, A_47, C_48]: (k2_relat_1(k5_relat_1(k7_relat_1(B_46, A_47), C_48))=k9_relat_1(k5_relat_1(B_46, C_48), A_47) | ~v1_relat_1(k5_relat_1(B_46, C_48)) | ~v1_relat_1(C_48) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_98, c_12])).
% 2.23/1.42  tff(c_192, plain, (![B_57, C_58]: (k9_relat_1(k5_relat_1(B_57, C_58), k1_relat_1(B_57))=k2_relat_1(k5_relat_1(B_57, C_58)) | ~v1_relat_1(k5_relat_1(B_57, C_58)) | ~v1_relat_1(C_58) | ~v1_relat_1(B_57) | ~v1_relat_1(B_57))), inference(superposition, [status(thm), theory('equality')], [c_50, c_118])).
% 2.23/1.42  tff(c_14, plain, (![B_15, C_17, A_14]: (k9_relat_1(k5_relat_1(B_15, C_17), A_14)=k9_relat_1(C_17, k9_relat_1(B_15, A_14)) | ~v1_relat_1(C_17) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.42  tff(c_211, plain, (![C_59, B_60]: (k9_relat_1(C_59, k9_relat_1(B_60, k1_relat_1(B_60)))=k2_relat_1(k5_relat_1(B_60, C_59)) | ~v1_relat_1(C_59) | ~v1_relat_1(B_60) | ~v1_relat_1(k5_relat_1(B_60, C_59)) | ~v1_relat_1(C_59) | ~v1_relat_1(B_60) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_192, c_14])).
% 2.23/1.42  tff(c_235, plain, (![C_61, B_62]: (k9_relat_1(C_61, k2_relat_1(B_62))=k2_relat_1(k5_relat_1(B_62, C_61)) | ~v1_relat_1(C_61) | ~v1_relat_1(B_62) | ~v1_relat_1(k5_relat_1(B_62, C_61)) | ~v1_relat_1(C_61) | ~v1_relat_1(B_62) | ~v1_relat_1(B_62) | ~v1_relat_1(B_62) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_57, c_211])).
% 2.23/1.42  tff(c_261, plain, (![B_67, A_68]: (k9_relat_1(B_67, k2_relat_1(A_68))=k2_relat_1(k5_relat_1(A_68, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_8, c_235])).
% 2.23/1.42  tff(c_18, plain, (k9_relat_1('#skF_3', k2_relat_1('#skF_2'))!=k2_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.42  tff(c_271, plain, (~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_261, c_18])).
% 2.23/1.42  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_271])).
% 2.23/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.42  
% 2.23/1.42  Inference rules
% 2.23/1.42  ----------------------
% 2.23/1.42  #Ref     : 0
% 2.23/1.42  #Sup     : 67
% 2.23/1.42  #Fact    : 0
% 2.23/1.42  #Define  : 0
% 2.23/1.42  #Split   : 0
% 2.23/1.42  #Chain   : 0
% 2.23/1.42  #Close   : 0
% 2.23/1.42  
% 2.23/1.42  Ordering : KBO
% 2.23/1.42  
% 2.23/1.42  Simplification rules
% 2.23/1.42  ----------------------
% 2.23/1.42  #Subsume      : 8
% 2.23/1.42  #Demod        : 2
% 2.23/1.42  #Tautology    : 24
% 2.23/1.42  #SimpNegUnit  : 0
% 2.23/1.42  #BackRed      : 0
% 2.23/1.42  
% 2.23/1.42  #Partial instantiations: 0
% 2.23/1.42  #Strategies tried      : 1
% 2.23/1.42  
% 2.23/1.42  Timing (in seconds)
% 2.23/1.42  ----------------------
% 2.23/1.43  Preprocessing        : 0.33
% 2.23/1.43  Parsing              : 0.17
% 2.23/1.43  CNF conversion       : 0.02
% 2.23/1.43  Main loop            : 0.24
% 2.23/1.43  Inferencing          : 0.11
% 2.23/1.43  Reduction            : 0.06
% 2.23/1.43  Demodulation         : 0.04
% 2.23/1.43  BG Simplification    : 0.02
% 2.23/1.43  Subsumption          : 0.04
% 2.23/1.43  Abstraction          : 0.02
% 2.23/1.43  MUC search           : 0.00
% 2.23/1.43  Cooper               : 0.00
% 2.23/1.43  Total                : 0.60
% 2.23/1.43  Index Insertion      : 0.00
% 2.23/1.43  Index Deletion       : 0.00
% 2.23/1.43  Index Matching       : 0.00
% 2.23/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
