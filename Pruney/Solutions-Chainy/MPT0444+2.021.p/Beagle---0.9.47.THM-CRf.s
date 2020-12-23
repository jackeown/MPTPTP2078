%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:23 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   57 (  98 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 137 expanded)
%              Number of equality atoms :    4 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k3_xboole_0(A_6,B_7),k3_xboole_0(A_6,C_8)) = k3_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] : r1_tarski(k2_xboole_0(k3_xboole_0(A_10,B_11),k3_xboole_0(A_10,C_12)),k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_162,plain,(
    ! [A_57,B_58,C_59] : r1_tarski(k3_xboole_0(A_57,k2_xboole_0(B_58,C_59)),k2_xboole_0(B_58,C_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_174,plain,(
    ! [A_57,A_14,B_15] : r1_tarski(k3_xboole_0(A_57,A_14),k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_162])).

tff(c_184,plain,(
    ! [A_60,A_61] : r1_tarski(k3_xboole_0(A_60,A_61),A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_174])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_92,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_96,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(A_22)
      | ~ v1_relat_1(B_23)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_92])).

tff(c_191,plain,(
    ! [A_60,A_61] :
      ( v1_relat_1(k3_xboole_0(A_60,A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_184,c_96])).

tff(c_181,plain,(
    ! [A_57,A_14] : r1_tarski(k3_xboole_0(A_57,A_14),A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_174])).

tff(c_238,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k2_relat_1(A_69),k2_relat_1(B_70))
      | ~ r1_tarski(A_69,B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_215,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k2_relat_1(A_67),k2_relat_1(B_68))
      | ~ r1_tarski(A_67,B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_194,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(A_62,k3_xboole_0(B_63,C_64))
      | ~ r1_tarski(A_62,C_64)
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_205,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_194,c_32])).

tff(c_214,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_218,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_215,c_214])).

tff(c_224,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2,c_218])).

tff(c_228,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_191,c_224])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_228])).

tff(c_236,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_241,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_238,c_236])).

tff(c_247,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_181,c_241])).

tff(c_251,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_191,c_247])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_251])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.31  
% 2.02/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.31  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.02/1.31  
% 2.02/1.31  %Foreground sorts:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Background operators:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Foreground operators:
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.02/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.02/1.31  
% 2.28/1.33  tff(f_79, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 2.28/1.33  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.28/1.33  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.28/1.33  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.28/1.33  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.28/1.33  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.28/1.33  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.28/1.33  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.28/1.33  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.28/1.33  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.33  tff(c_14, plain, (![A_14, B_15]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.33  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k3_xboole_0(A_6, B_7), k3_xboole_0(A_6, C_8))=k3_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.33  tff(c_10, plain, (![A_10, B_11, C_12]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_10, B_11), k3_xboole_0(A_10, C_12)), k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.33  tff(c_162, plain, (![A_57, B_58, C_59]: (r1_tarski(k3_xboole_0(A_57, k2_xboole_0(B_58, C_59)), k2_xboole_0(B_58, C_59)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 2.28/1.33  tff(c_174, plain, (![A_57, A_14, B_15]: (r1_tarski(k3_xboole_0(A_57, A_14), k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))))), inference(superposition, [status(thm), theory('equality')], [c_14, c_162])).
% 2.28/1.33  tff(c_184, plain, (![A_60, A_61]: (r1_tarski(k3_xboole_0(A_60, A_61), A_61))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_174])).
% 2.28/1.33  tff(c_24, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.28/1.33  tff(c_92, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.28/1.33  tff(c_96, plain, (![A_22, B_23]: (v1_relat_1(A_22) | ~v1_relat_1(B_23) | ~r1_tarski(A_22, B_23))), inference(resolution, [status(thm)], [c_24, c_92])).
% 2.28/1.33  tff(c_191, plain, (![A_60, A_61]: (v1_relat_1(k3_xboole_0(A_60, A_61)) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_184, c_96])).
% 2.28/1.33  tff(c_181, plain, (![A_57, A_14]: (r1_tarski(k3_xboole_0(A_57, A_14), A_14))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_174])).
% 2.28/1.33  tff(c_238, plain, (![A_69, B_70]: (r1_tarski(k2_relat_1(A_69), k2_relat_1(B_70)) | ~r1_tarski(A_69, B_70) | ~v1_relat_1(B_70) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.28/1.33  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.33  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.33  tff(c_215, plain, (![A_67, B_68]: (r1_tarski(k2_relat_1(A_67), k2_relat_1(B_68)) | ~r1_tarski(A_67, B_68) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.28/1.33  tff(c_194, plain, (![A_62, B_63, C_64]: (r1_tarski(A_62, k3_xboole_0(B_63, C_64)) | ~r1_tarski(A_62, C_64) | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.33  tff(c_32, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.28/1.33  tff(c_205, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_194, c_32])).
% 2.28/1.33  tff(c_214, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_205])).
% 2.28/1.33  tff(c_218, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_215, c_214])).
% 2.28/1.33  tff(c_224, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2, c_218])).
% 2.28/1.33  tff(c_228, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_191, c_224])).
% 2.28/1.33  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_228])).
% 2.28/1.33  tff(c_236, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_205])).
% 2.28/1.33  tff(c_241, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_238, c_236])).
% 2.28/1.33  tff(c_247, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_181, c_241])).
% 2.28/1.33  tff(c_251, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_191, c_247])).
% 2.28/1.33  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_251])).
% 2.28/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.33  
% 2.28/1.33  Inference rules
% 2.28/1.33  ----------------------
% 2.28/1.33  #Ref     : 0
% 2.28/1.33  #Sup     : 45
% 2.28/1.33  #Fact    : 0
% 2.28/1.33  #Define  : 0
% 2.28/1.33  #Split   : 2
% 2.28/1.33  #Chain   : 0
% 2.28/1.33  #Close   : 0
% 2.28/1.33  
% 2.28/1.33  Ordering : KBO
% 2.28/1.33  
% 2.28/1.33  Simplification rules
% 2.28/1.33  ----------------------
% 2.28/1.33  #Subsume      : 3
% 2.28/1.33  #Demod        : 24
% 2.28/1.33  #Tautology    : 26
% 2.28/1.33  #SimpNegUnit  : 4
% 2.28/1.33  #BackRed      : 2
% 2.28/1.33  
% 2.28/1.33  #Partial instantiations: 0
% 2.28/1.33  #Strategies tried      : 1
% 2.28/1.33  
% 2.28/1.33  Timing (in seconds)
% 2.28/1.33  ----------------------
% 2.28/1.33  Preprocessing        : 0.33
% 2.28/1.33  Parsing              : 0.18
% 2.28/1.33  CNF conversion       : 0.02
% 2.28/1.33  Main loop            : 0.17
% 2.28/1.33  Inferencing          : 0.06
% 2.28/1.33  Reduction            : 0.06
% 2.28/1.33  Demodulation         : 0.04
% 2.28/1.33  BG Simplification    : 0.01
% 2.28/1.33  Subsumption          : 0.02
% 2.28/1.33  Abstraction          : 0.01
% 2.28/1.33  MUC search           : 0.00
% 2.28/1.33  Cooper               : 0.00
% 2.28/1.33  Total                : 0.53
% 2.28/1.33  Index Insertion      : 0.00
% 2.28/1.33  Index Deletion       : 0.00
% 2.28/1.33  Index Matching       : 0.00
% 2.28/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
