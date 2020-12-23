%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:47 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 133 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 191 expanded)
%              Number of equality atoms :   10 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,(
    ! [B_43,A_44] : k1_setfam_1(k2_tarski(B_43,A_44)) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_64])).

tff(c_16,plain,(
    ! [A_18,B_19] : k1_setfam_1(k2_tarski(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,A_46) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_16])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_130,plain,(
    ! [A_46,B_45] :
      ( v1_relat_1(k3_xboole_0(A_46,B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_18])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [C_28,A_22,B_26] :
      ( r1_tarski(k5_relat_1(C_28,A_22),k5_relat_1(C_28,B_26))
      | ~ r1_tarski(A_22,B_26)
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_133,plain,(
    ! [B_45,A_46] : r1_tarski(k3_xboole_0(B_45,A_46),A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,k4_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_265,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(A_66,k4_xboole_0(B_67,C_68))
      | ~ r1_xboole_0(A_66,C_68)
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_526,plain,(
    ! [A_86,A_87,B_88] :
      ( r1_tarski(A_86,k3_xboole_0(A_87,B_88))
      | ~ r1_xboole_0(A_86,k4_xboole_0(A_87,B_88))
      | ~ r1_tarski(A_86,A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_265])).

tff(c_583,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_tarski(A_91,k3_xboole_0(C_92,B_93))
      | ~ r1_tarski(A_91,C_92)
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_526])).

tff(c_94,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_16])).

tff(c_22,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_111,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_22])).

tff(c_599,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_583,c_111])).

tff(c_757,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_599])).

tff(c_760,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_757])).

tff(c_763,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_133,c_760])).

tff(c_766,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_763])).

tff(c_773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_766])).

tff(c_774,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_599])).

tff(c_778,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_774])).

tff(c_781,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_2,c_778])).

tff(c_784,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_781])).

tff(c_791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.48  
% 3.18/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.48  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.18/1.48  
% 3.18/1.48  %Foreground sorts:
% 3.18/1.48  
% 3.18/1.48  
% 3.18/1.48  %Background operators:
% 3.18/1.48  
% 3.18/1.48  
% 3.18/1.48  %Foreground operators:
% 3.18/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.18/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.18/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.18/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.18/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.18/1.48  
% 3.36/1.50  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 3.36/1.50  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.36/1.50  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.36/1.50  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 3.36/1.50  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.36/1.50  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 3.36/1.50  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.36/1.50  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.36/1.50  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.36/1.50  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.50  tff(c_10, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.50  tff(c_64, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.50  tff(c_88, plain, (![B_43, A_44]: (k1_setfam_1(k2_tarski(B_43, A_44))=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_10, c_64])).
% 3.36/1.50  tff(c_16, plain, (![A_18, B_19]: (k1_setfam_1(k2_tarski(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.50  tff(c_112, plain, (![B_45, A_46]: (k3_xboole_0(B_45, A_46)=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_88, c_16])).
% 3.36/1.50  tff(c_18, plain, (![A_20, B_21]: (v1_relat_1(k3_xboole_0(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.50  tff(c_130, plain, (![A_46, B_45]: (v1_relat_1(k3_xboole_0(A_46, B_45)) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_112, c_18])).
% 3.36/1.50  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.50  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.50  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.36/1.50  tff(c_20, plain, (![C_28, A_22, B_26]: (r1_tarski(k5_relat_1(C_28, A_22), k5_relat_1(C_28, B_26)) | ~r1_tarski(A_22, B_26) | ~v1_relat_1(C_28) | ~v1_relat_1(B_26) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.50  tff(c_133, plain, (![B_45, A_46]: (r1_tarski(k3_xboole_0(B_45, A_46), A_46))), inference(superposition, [status(thm), theory('equality')], [c_112, c_2])).
% 3.36/1.50  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, k4_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.50  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.50  tff(c_265, plain, (![A_66, B_67, C_68]: (r1_tarski(A_66, k4_xboole_0(B_67, C_68)) | ~r1_xboole_0(A_66, C_68) | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.50  tff(c_526, plain, (![A_86, A_87, B_88]: (r1_tarski(A_86, k3_xboole_0(A_87, B_88)) | ~r1_xboole_0(A_86, k4_xboole_0(A_87, B_88)) | ~r1_tarski(A_86, A_87))), inference(superposition, [status(thm), theory('equality')], [c_4, c_265])).
% 3.36/1.50  tff(c_583, plain, (![A_91, C_92, B_93]: (r1_tarski(A_91, k3_xboole_0(C_92, B_93)) | ~r1_tarski(A_91, C_92) | ~r1_tarski(A_91, B_93))), inference(resolution, [status(thm)], [c_6, c_526])).
% 3.36/1.50  tff(c_94, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_88, c_16])).
% 3.36/1.50  tff(c_22, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.36/1.50  tff(c_111, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_22])).
% 3.36/1.50  tff(c_599, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_583, c_111])).
% 3.36/1.50  tff(c_757, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_599])).
% 3.36/1.50  tff(c_760, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_757])).
% 3.36/1.50  tff(c_763, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_133, c_760])).
% 3.36/1.50  tff(c_766, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_130, c_763])).
% 3.36/1.50  tff(c_773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_766])).
% 3.36/1.50  tff(c_774, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_599])).
% 3.36/1.50  tff(c_778, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_774])).
% 3.36/1.50  tff(c_781, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_2, c_778])).
% 3.36/1.50  tff(c_784, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_130, c_781])).
% 3.36/1.50  tff(c_791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_784])).
% 3.36/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.50  
% 3.36/1.50  Inference rules
% 3.36/1.50  ----------------------
% 3.36/1.50  #Ref     : 0
% 3.36/1.50  #Sup     : 196
% 3.36/1.50  #Fact    : 0
% 3.36/1.50  #Define  : 0
% 3.36/1.50  #Split   : 1
% 3.36/1.50  #Chain   : 0
% 3.36/1.50  #Close   : 0
% 3.36/1.50  
% 3.36/1.50  Ordering : KBO
% 3.36/1.50  
% 3.36/1.50  Simplification rules
% 3.36/1.50  ----------------------
% 3.36/1.50  #Subsume      : 20
% 3.36/1.50  #Demod        : 85
% 3.36/1.50  #Tautology    : 82
% 3.36/1.50  #SimpNegUnit  : 0
% 3.36/1.50  #BackRed      : 1
% 3.36/1.50  
% 3.36/1.50  #Partial instantiations: 0
% 3.36/1.50  #Strategies tried      : 1
% 3.36/1.50  
% 3.36/1.50  Timing (in seconds)
% 3.36/1.50  ----------------------
% 3.36/1.50  Preprocessing        : 0.31
% 3.36/1.51  Parsing              : 0.16
% 3.36/1.51  CNF conversion       : 0.02
% 3.36/1.51  Main loop            : 0.40
% 3.36/1.51  Inferencing          : 0.14
% 3.36/1.51  Reduction            : 0.16
% 3.36/1.51  Demodulation         : 0.13
% 3.36/1.51  BG Simplification    : 0.02
% 3.36/1.51  Subsumption          : 0.07
% 3.36/1.51  Abstraction          : 0.02
% 3.36/1.51  MUC search           : 0.00
% 3.36/1.51  Cooper               : 0.00
% 3.36/1.51  Total                : 0.75
% 3.36/1.51  Index Insertion      : 0.00
% 3.36/1.51  Index Deletion       : 0.00
% 3.36/1.51  Index Matching       : 0.00
% 3.36/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
