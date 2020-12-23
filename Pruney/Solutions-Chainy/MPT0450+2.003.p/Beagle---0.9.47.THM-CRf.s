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
% DateTime   : Thu Dec  3 09:58:36 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   51 (  93 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 137 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(B_32,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_59])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [B_32,A_31] : k3_xboole_0(B_32,A_31) = k3_xboole_0(A_31,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_167,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(A_41)
      | ~ v1_relat_1(B_42)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_14,c_162])).

tff(c_176,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k3_xboole_0(A_43,B_44))
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_2,c_167])).

tff(c_179,plain,(
    ! [B_32,A_31] :
      ( v1_relat_1(k3_xboole_0(B_32,A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_176])).

tff(c_103,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_10])).

tff(c_118,plain,(
    ! [B_33,A_34] : r1_tarski(k3_xboole_0(B_33,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_2])).

tff(c_18,plain,(
    ! [A_17,B_19] :
      ( r1_tarski(k3_relat_1(A_17),k3_relat_1(B_19))
      | ~ r1_tarski(A_17,B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_190,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(A_47,k3_xboole_0(B_48,C_49))
      | ~ r1_tarski(A_47,C_49)
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_204,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_190,c_20])).

tff(c_222,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_225,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_222])).

tff(c_228,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2,c_225])).

tff(c_231,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_179,c_228])).

tff(c_238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_231])).

tff(c_239,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_243,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_239])).

tff(c_246,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_118,c_243])).

tff(c_253,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_179,c_246])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:41:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.23  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 1.95/1.23  
% 1.95/1.23  %Foreground sorts:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Background operators:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Foreground operators:
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.23  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.95/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.95/1.23  
% 2.10/1.24  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.10/1.24  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.10/1.24  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.10/1.24  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.10/1.24  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.10/1.24  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.10/1.24  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.10/1.24  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.10/1.24  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.24  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.24  tff(c_59, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.24  tff(c_80, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(B_32, A_31))), inference(superposition, [status(thm), theory('equality')], [c_6, c_59])).
% 2.10/1.24  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.24  tff(c_86, plain, (![B_32, A_31]: (k3_xboole_0(B_32, A_31)=k3_xboole_0(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_80, c_10])).
% 2.10/1.24  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.24  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.24  tff(c_162, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.24  tff(c_167, plain, (![A_41, B_42]: (v1_relat_1(A_41) | ~v1_relat_1(B_42) | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_14, c_162])).
% 2.10/1.24  tff(c_176, plain, (![A_43, B_44]: (v1_relat_1(k3_xboole_0(A_43, B_44)) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_2, c_167])).
% 2.10/1.24  tff(c_179, plain, (![B_32, A_31]: (v1_relat_1(k3_xboole_0(B_32, A_31)) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_86, c_176])).
% 2.10/1.24  tff(c_103, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_80, c_10])).
% 2.10/1.24  tff(c_118, plain, (![B_33, A_34]: (r1_tarski(k3_xboole_0(B_33, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_103, c_2])).
% 2.10/1.24  tff(c_18, plain, (![A_17, B_19]: (r1_tarski(k3_relat_1(A_17), k3_relat_1(B_19)) | ~r1_tarski(A_17, B_19) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.24  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.24  tff(c_190, plain, (![A_47, B_48, C_49]: (r1_tarski(A_47, k3_xboole_0(B_48, C_49)) | ~r1_tarski(A_47, C_49) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.24  tff(c_20, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.24  tff(c_204, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_190, c_20])).
% 2.10/1.24  tff(c_222, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_204])).
% 2.10/1.24  tff(c_225, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_222])).
% 2.10/1.24  tff(c_228, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2, c_225])).
% 2.10/1.24  tff(c_231, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_179, c_228])).
% 2.10/1.24  tff(c_238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_231])).
% 2.10/1.24  tff(c_239, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_204])).
% 2.10/1.24  tff(c_243, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_239])).
% 2.10/1.24  tff(c_246, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_118, c_243])).
% 2.10/1.24  tff(c_253, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_179, c_246])).
% 2.10/1.24  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_253])).
% 2.10/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  Inference rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Ref     : 0
% 2.10/1.24  #Sup     : 56
% 2.10/1.24  #Fact    : 0
% 2.10/1.24  #Define  : 0
% 2.10/1.24  #Split   : 1
% 2.10/1.24  #Chain   : 0
% 2.10/1.24  #Close   : 0
% 2.10/1.24  
% 2.10/1.24  Ordering : KBO
% 2.10/1.24  
% 2.10/1.24  Simplification rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Subsume      : 11
% 2.10/1.24  #Demod        : 12
% 2.10/1.24  #Tautology    : 29
% 2.10/1.24  #SimpNegUnit  : 0
% 2.10/1.24  #BackRed      : 0
% 2.10/1.24  
% 2.10/1.24  #Partial instantiations: 0
% 2.10/1.24  #Strategies tried      : 1
% 2.10/1.24  
% 2.10/1.24  Timing (in seconds)
% 2.10/1.24  ----------------------
% 2.10/1.24  Preprocessing        : 0.29
% 2.10/1.24  Parsing              : 0.16
% 2.10/1.24  CNF conversion       : 0.02
% 2.10/1.24  Main loop            : 0.18
% 2.10/1.24  Inferencing          : 0.07
% 2.10/1.24  Reduction            : 0.06
% 2.10/1.24  Demodulation         : 0.05
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.03
% 2.10/1.24  Abstraction          : 0.01
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.50
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.25  Index Matching       : 0.00
% 2.10/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
