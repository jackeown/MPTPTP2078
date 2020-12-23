%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:39 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  90 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 129 expanded)
%              Number of equality atoms :    4 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_141,plain,(
    ! [A_58,B_59,C_60] : r1_tarski(k2_xboole_0(k3_xboole_0(A_58,B_59),k3_xboole_0(A_58,C_60)),k2_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_148,plain,(
    ! [A_58,B_59] : r1_tarski(k3_xboole_0(A_58,B_59),k2_xboole_0(B_59,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_141])).

tff(c_155,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),B_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_148])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_69,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(A_19)
      | ~ v1_relat_1(B_20)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_159,plain,(
    ! [A_61,B_62] :
      ( v1_relat_1(k3_xboole_0(A_61,B_62))
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_155,c_69])).

tff(c_153,plain,(
    ! [A_58,B_59] : r1_tarski(k3_xboole_0(A_58,B_59),B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_148])).

tff(c_24,plain,(
    ! [A_24,B_26] :
      ( r1_tarski(k3_relat_1(A_24),k3_relat_1(B_26))
      | ~ r1_tarski(A_24,B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_76,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [A_45,B_46] : r1_tarski(k3_xboole_0(A_45,B_46),A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_8])).

tff(c_132,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_tarski(A_55,k3_xboole_0(B_56,C_57))
      | ~ r1_tarski(A_55,C_57)
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_140,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_132,c_26])).

tff(c_167,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_170,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_167])).

tff(c_173,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_88,c_170])).

tff(c_176,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_159,c_173])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_176])).

tff(c_184,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_188,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_184])).

tff(c_191,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_153,c_188])).

tff(c_198,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_159,c_191])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:46:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.24  
% 2.22/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.24  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.22/1.24  
% 2.22/1.24  %Foreground sorts:
% 2.22/1.24  
% 2.22/1.24  
% 2.22/1.24  %Background operators:
% 2.22/1.24  
% 2.22/1.24  
% 2.22/1.24  %Foreground operators:
% 2.22/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.24  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.22/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.22/1.24  
% 2.22/1.25  tff(f_73, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.22/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.22/1.25  tff(f_35, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.22/1.25  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.22/1.25  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.22/1.25  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.22/1.25  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.22/1.25  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.22/1.25  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.22/1.25  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.25  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.25  tff(c_141, plain, (![A_58, B_59, C_60]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_58, B_59), k3_xboole_0(A_58, C_60)), k2_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.25  tff(c_148, plain, (![A_58, B_59]: (r1_tarski(k3_xboole_0(A_58, B_59), k2_xboole_0(B_59, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_141])).
% 2.22/1.25  tff(c_155, plain, (![A_61, B_62]: (r1_tarski(k3_xboole_0(A_61, B_62), B_62))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_148])).
% 2.22/1.25  tff(c_20, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.22/1.25  tff(c_65, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.25  tff(c_69, plain, (![A_19, B_20]: (v1_relat_1(A_19) | ~v1_relat_1(B_20) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_20, c_65])).
% 2.22/1.25  tff(c_159, plain, (![A_61, B_62]: (v1_relat_1(k3_xboole_0(A_61, B_62)) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_155, c_69])).
% 2.22/1.25  tff(c_153, plain, (![A_58, B_59]: (r1_tarski(k3_xboole_0(A_58, B_59), B_59))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_148])).
% 2.22/1.25  tff(c_24, plain, (![A_24, B_26]: (r1_tarski(k3_relat_1(A_24), k3_relat_1(B_26)) | ~r1_tarski(A_24, B_26) | ~v1_relat_1(B_26) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.25  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.25  tff(c_76, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.25  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.25  tff(c_88, plain, (![A_45, B_46]: (r1_tarski(k3_xboole_0(A_45, B_46), A_45))), inference(superposition, [status(thm), theory('equality')], [c_76, c_8])).
% 2.22/1.25  tff(c_132, plain, (![A_55, B_56, C_57]: (r1_tarski(A_55, k3_xboole_0(B_56, C_57)) | ~r1_tarski(A_55, C_57) | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.25  tff(c_26, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.25  tff(c_140, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_132, c_26])).
% 2.22/1.25  tff(c_167, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_140])).
% 2.22/1.25  tff(c_170, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_167])).
% 2.22/1.25  tff(c_173, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_88, c_170])).
% 2.22/1.25  tff(c_176, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_159, c_173])).
% 2.22/1.25  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_176])).
% 2.22/1.25  tff(c_184, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_140])).
% 2.22/1.25  tff(c_188, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_184])).
% 2.22/1.25  tff(c_191, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_153, c_188])).
% 2.22/1.25  tff(c_198, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_159, c_191])).
% 2.22/1.25  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_198])).
% 2.22/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.25  
% 2.22/1.25  Inference rules
% 2.22/1.25  ----------------------
% 2.22/1.25  #Ref     : 0
% 2.22/1.25  #Sup     : 37
% 2.22/1.25  #Fact    : 0
% 2.22/1.25  #Define  : 0
% 2.22/1.25  #Split   : 1
% 2.22/1.25  #Chain   : 0
% 2.22/1.25  #Close   : 0
% 2.22/1.25  
% 2.22/1.25  Ordering : KBO
% 2.22/1.25  
% 2.22/1.25  Simplification rules
% 2.22/1.25  ----------------------
% 2.22/1.25  #Subsume      : 2
% 2.22/1.25  #Demod        : 11
% 2.22/1.25  #Tautology    : 16
% 2.22/1.25  #SimpNegUnit  : 0
% 2.22/1.25  #BackRed      : 0
% 2.22/1.25  
% 2.22/1.25  #Partial instantiations: 0
% 2.22/1.25  #Strategies tried      : 1
% 2.22/1.25  
% 2.22/1.25  Timing (in seconds)
% 2.22/1.25  ----------------------
% 2.22/1.26  Preprocessing        : 0.30
% 2.22/1.26  Parsing              : 0.16
% 2.22/1.26  CNF conversion       : 0.02
% 2.22/1.26  Main loop            : 0.16
% 2.22/1.26  Inferencing          : 0.07
% 2.22/1.26  Reduction            : 0.05
% 2.22/1.26  Demodulation         : 0.04
% 2.22/1.26  BG Simplification    : 0.01
% 2.22/1.26  Subsumption          : 0.03
% 2.22/1.26  Abstraction          : 0.01
% 2.22/1.26  MUC search           : 0.00
% 2.22/1.26  Cooper               : 0.00
% 2.22/1.26  Total                : 0.49
% 2.22/1.26  Index Insertion      : 0.00
% 2.22/1.26  Index Deletion       : 0.00
% 2.22/1.26  Index Matching       : 0.00
% 2.22/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
