%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:20 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 107 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 151 expanded)
%              Number of equality atoms :    9 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

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

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [B_35,A_36] : k1_setfam_1(k2_tarski(B_35,A_36)) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [B_35,A_36] : k3_xboole_0(B_35,A_36) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_12])).

tff(c_150,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_159,plain,(
    ! [A_39,B_40] : r1_tarski(k3_xboole_0(A_39,B_40),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_4])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_175,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_190,plain,(
    ! [A_47,B_48] :
      ( v1_relat_1(A_47)
      | ~ v1_relat_1(B_48)
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_16,c_175])).

tff(c_222,plain,(
    ! [A_54,B_55] :
      ( v1_relat_1(k3_xboole_0(A_54,B_55))
      | ~ v1_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_159,c_190])).

tff(c_225,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(k3_xboole_0(B_35,A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_222])).

tff(c_168,plain,(
    ! [A_41,B_42] : r1_tarski(k3_xboole_0(A_41,B_42),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_4])).

tff(c_171,plain,(
    ! [B_35,A_36] : r1_tarski(k3_xboole_0(B_35,A_36),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_168])).

tff(c_20,plain,(
    ! [A_19,B_21] :
      ( r1_tarski(k2_relat_1(A_19),k2_relat_1(B_21))
      | ~ r1_tarski(A_19,B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_203,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(A_49,k3_xboole_0(B_50,C_51))
      | ~ r1_tarski(A_49,C_51)
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_217,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_203,c_24])).

tff(c_267,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_270,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_267])).

tff(c_273,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_159,c_270])).

tff(c_276,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_225,c_273])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_276])).

tff(c_284,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_288,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_284])).

tff(c_291,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_171,c_288])).

tff(c_294,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_225,c_291])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.25  
% 2.09/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.25  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.09/1.25  
% 2.09/1.25  %Foreground sorts:
% 2.09/1.25  
% 2.09/1.25  
% 2.09/1.25  %Background operators:
% 2.09/1.25  
% 2.09/1.25  
% 2.09/1.25  %Foreground operators:
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.09/1.25  
% 2.09/1.26  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 2.09/1.26  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.09/1.26  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.09/1.26  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.09/1.26  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.09/1.26  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.09/1.26  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.09/1.26  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.09/1.26  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.09/1.26  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.09/1.26  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.26  tff(c_64, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.26  tff(c_93, plain, (![B_35, A_36]: (k1_setfam_1(k2_tarski(B_35, A_36))=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_8, c_64])).
% 2.09/1.26  tff(c_12, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.26  tff(c_99, plain, (![B_35, A_36]: (k3_xboole_0(B_35, A_36)=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_93, c_12])).
% 2.09/1.26  tff(c_150, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.26  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.26  tff(c_159, plain, (![A_39, B_40]: (r1_tarski(k3_xboole_0(A_39, B_40), A_39))), inference(superposition, [status(thm), theory('equality')], [c_150, c_4])).
% 2.09/1.26  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.26  tff(c_175, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.09/1.26  tff(c_190, plain, (![A_47, B_48]: (v1_relat_1(A_47) | ~v1_relat_1(B_48) | ~r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_16, c_175])).
% 2.09/1.26  tff(c_222, plain, (![A_54, B_55]: (v1_relat_1(k3_xboole_0(A_54, B_55)) | ~v1_relat_1(A_54))), inference(resolution, [status(thm)], [c_159, c_190])).
% 2.09/1.26  tff(c_225, plain, (![B_35, A_36]: (v1_relat_1(k3_xboole_0(B_35, A_36)) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_99, c_222])).
% 2.09/1.26  tff(c_168, plain, (![A_41, B_42]: (r1_tarski(k3_xboole_0(A_41, B_42), A_41))), inference(superposition, [status(thm), theory('equality')], [c_150, c_4])).
% 2.09/1.26  tff(c_171, plain, (![B_35, A_36]: (r1_tarski(k3_xboole_0(B_35, A_36), A_36))), inference(superposition, [status(thm), theory('equality')], [c_99, c_168])).
% 2.09/1.26  tff(c_20, plain, (![A_19, B_21]: (r1_tarski(k2_relat_1(A_19), k2_relat_1(B_21)) | ~r1_tarski(A_19, B_21) | ~v1_relat_1(B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.09/1.26  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.09/1.26  tff(c_203, plain, (![A_49, B_50, C_51]: (r1_tarski(A_49, k3_xboole_0(B_50, C_51)) | ~r1_tarski(A_49, C_51) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.26  tff(c_24, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.09/1.26  tff(c_217, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_203, c_24])).
% 2.09/1.26  tff(c_267, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_217])).
% 2.09/1.26  tff(c_270, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_267])).
% 2.09/1.26  tff(c_273, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_159, c_270])).
% 2.09/1.26  tff(c_276, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_225, c_273])).
% 2.09/1.26  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_276])).
% 2.09/1.26  tff(c_284, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_217])).
% 2.09/1.26  tff(c_288, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_284])).
% 2.09/1.26  tff(c_291, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_171, c_288])).
% 2.09/1.26  tff(c_294, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_225, c_291])).
% 2.09/1.26  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_294])).
% 2.09/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.26  
% 2.09/1.26  Inference rules
% 2.09/1.26  ----------------------
% 2.09/1.26  #Ref     : 0
% 2.09/1.26  #Sup     : 65
% 2.09/1.26  #Fact    : 0
% 2.09/1.26  #Define  : 0
% 2.09/1.26  #Split   : 1
% 2.09/1.26  #Chain   : 0
% 2.09/1.26  #Close   : 0
% 2.09/1.26  
% 2.09/1.26  Ordering : KBO
% 2.09/1.26  
% 2.09/1.26  Simplification rules
% 2.09/1.26  ----------------------
% 2.09/1.26  #Subsume      : 9
% 2.09/1.26  #Demod        : 14
% 2.09/1.26  #Tautology    : 35
% 2.09/1.26  #SimpNegUnit  : 0
% 2.09/1.26  #BackRed      : 0
% 2.09/1.26  
% 2.09/1.26  #Partial instantiations: 0
% 2.09/1.26  #Strategies tried      : 1
% 2.09/1.26  
% 2.09/1.26  Timing (in seconds)
% 2.09/1.26  ----------------------
% 2.09/1.26  Preprocessing        : 0.30
% 2.09/1.26  Parsing              : 0.16
% 2.09/1.26  CNF conversion       : 0.02
% 2.09/1.26  Main loop            : 0.19
% 2.09/1.26  Inferencing          : 0.07
% 2.09/1.26  Reduction            : 0.06
% 2.09/1.26  Demodulation         : 0.05
% 2.09/1.26  BG Simplification    : 0.01
% 2.09/1.26  Subsumption          : 0.03
% 2.09/1.26  Abstraction          : 0.01
% 2.09/1.26  MUC search           : 0.00
% 2.09/1.26  Cooper               : 0.00
% 2.09/1.26  Total                : 0.53
% 2.09/1.26  Index Insertion      : 0.00
% 2.09/1.26  Index Deletion       : 0.00
% 2.09/1.27  Index Matching       : 0.00
% 2.09/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
