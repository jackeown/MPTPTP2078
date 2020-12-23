%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:36 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 106 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 149 expanded)
%              Number of equality atoms :    9 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(B_36,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_61])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,(
    ! [B_36,A_35] : k3_xboole_0(B_36,A_35) = k3_xboole_0(A_35,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_12])).

tff(c_158,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_176,plain,(
    ! [A_45,B_46] : r1_tarski(k3_xboole_0(A_45,B_46),A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_4])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_152,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(A_14)
      | ~ v1_relat_1(B_15)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_16,c_148])).

tff(c_220,plain,(
    ! [A_54,B_55] :
      ( v1_relat_1(k3_xboole_0(A_54,B_55))
      | ~ v1_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_176,c_152])).

tff(c_223,plain,(
    ! [B_36,A_35] :
      ( v1_relat_1(k3_xboole_0(B_36,A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_220])).

tff(c_182,plain,(
    ! [B_36,A_35] : r1_tarski(k3_xboole_0(B_36,A_35),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_176])).

tff(c_20,plain,(
    ! [A_19,B_21] :
      ( r1_tarski(k3_relat_1(A_19),k3_relat_1(B_21))
      | ~ r1_tarski(A_19,B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_167,plain,(
    ! [A_43,B_44] : r1_tarski(k3_xboole_0(A_43,B_44),A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_4])).

tff(c_201,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(A_49,k3_xboole_0(B_50,C_51))
      | ~ r1_tarski(A_49,C_51)
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_215,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_201,c_22])).

tff(c_265,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_268,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_265])).

tff(c_271,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_167,c_268])).

tff(c_274,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_223,c_271])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_274])).

tff(c_282,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_286,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_282])).

tff(c_289,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_182,c_286])).

tff(c_292,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_223,c_289])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.23  
% 1.84/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.08/1.23  
% 2.08/1.23  %Foreground sorts:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Background operators:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Foreground operators:
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.23  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.08/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.23  
% 2.08/1.24  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.08/1.24  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.08/1.24  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.08/1.24  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.08/1.24  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.08/1.24  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.08/1.24  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.08/1.24  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.08/1.24  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.08/1.24  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.24  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.24  tff(c_61, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.24  tff(c_91, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(B_36, A_35))), inference(superposition, [status(thm), theory('equality')], [c_8, c_61])).
% 2.08/1.24  tff(c_12, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.24  tff(c_97, plain, (![B_36, A_35]: (k3_xboole_0(B_36, A_35)=k3_xboole_0(A_35, B_36))), inference(superposition, [status(thm), theory('equality')], [c_91, c_12])).
% 2.08/1.24  tff(c_158, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.24  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.24  tff(c_176, plain, (![A_45, B_46]: (r1_tarski(k3_xboole_0(A_45, B_46), A_45))), inference(superposition, [status(thm), theory('equality')], [c_158, c_4])).
% 2.08/1.24  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.08/1.24  tff(c_148, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.24  tff(c_152, plain, (![A_14, B_15]: (v1_relat_1(A_14) | ~v1_relat_1(B_15) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_16, c_148])).
% 2.08/1.24  tff(c_220, plain, (![A_54, B_55]: (v1_relat_1(k3_xboole_0(A_54, B_55)) | ~v1_relat_1(A_54))), inference(resolution, [status(thm)], [c_176, c_152])).
% 2.08/1.24  tff(c_223, plain, (![B_36, A_35]: (v1_relat_1(k3_xboole_0(B_36, A_35)) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_97, c_220])).
% 2.08/1.24  tff(c_182, plain, (![B_36, A_35]: (r1_tarski(k3_xboole_0(B_36, A_35), A_35))), inference(superposition, [status(thm), theory('equality')], [c_97, c_176])).
% 2.08/1.24  tff(c_20, plain, (![A_19, B_21]: (r1_tarski(k3_relat_1(A_19), k3_relat_1(B_21)) | ~r1_tarski(A_19, B_21) | ~v1_relat_1(B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.24  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.24  tff(c_167, plain, (![A_43, B_44]: (r1_tarski(k3_xboole_0(A_43, B_44), A_43))), inference(superposition, [status(thm), theory('equality')], [c_158, c_4])).
% 2.08/1.24  tff(c_201, plain, (![A_49, B_50, C_51]: (r1_tarski(A_49, k3_xboole_0(B_50, C_51)) | ~r1_tarski(A_49, C_51) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.24  tff(c_22, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.24  tff(c_215, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_201, c_22])).
% 2.08/1.24  tff(c_265, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_215])).
% 2.08/1.24  tff(c_268, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_265])).
% 2.08/1.24  tff(c_271, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_167, c_268])).
% 2.08/1.24  tff(c_274, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_223, c_271])).
% 2.08/1.24  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_274])).
% 2.08/1.24  tff(c_282, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_215])).
% 2.08/1.24  tff(c_286, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_282])).
% 2.08/1.24  tff(c_289, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_182, c_286])).
% 2.08/1.24  tff(c_292, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_223, c_289])).
% 2.08/1.24  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_292])).
% 2.08/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  Inference rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Ref     : 0
% 2.08/1.24  #Sup     : 65
% 2.08/1.24  #Fact    : 0
% 2.08/1.24  #Define  : 0
% 2.08/1.24  #Split   : 1
% 2.08/1.24  #Chain   : 0
% 2.08/1.24  #Close   : 0
% 2.08/1.24  
% 2.08/1.24  Ordering : KBO
% 2.08/1.24  
% 2.08/1.24  Simplification rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Subsume      : 9
% 2.08/1.24  #Demod        : 14
% 2.08/1.24  #Tautology    : 35
% 2.08/1.24  #SimpNegUnit  : 0
% 2.08/1.24  #BackRed      : 0
% 2.08/1.24  
% 2.08/1.24  #Partial instantiations: 0
% 2.08/1.24  #Strategies tried      : 1
% 2.08/1.24  
% 2.08/1.24  Timing (in seconds)
% 2.08/1.24  ----------------------
% 2.08/1.25  Preprocessing        : 0.29
% 2.08/1.25  Parsing              : 0.16
% 2.08/1.25  CNF conversion       : 0.02
% 2.08/1.25  Main loop            : 0.19
% 2.08/1.25  Inferencing          : 0.07
% 2.08/1.25  Reduction            : 0.07
% 2.08/1.25  Demodulation         : 0.05
% 2.08/1.25  BG Simplification    : 0.01
% 2.08/1.25  Subsumption          : 0.03
% 2.08/1.25  Abstraction          : 0.01
% 2.08/1.25  MUC search           : 0.00
% 2.08/1.25  Cooper               : 0.00
% 2.08/1.25  Total                : 0.51
% 2.08/1.25  Index Insertion      : 0.00
% 2.08/1.25  Index Deletion       : 0.00
% 2.08/1.25  Index Matching       : 0.00
% 2.08/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
