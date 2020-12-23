%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:22 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   56 (  97 expanded)
%              Number of leaves         :   27 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 137 expanded)
%              Number of equality atoms :    4 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k3_xboole_0(A_8,B_9),k3_xboole_0(A_8,C_10)) = k3_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : r1_tarski(k2_xboole_0(k3_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)),k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    ! [A_54,B_55,C_56] : r1_tarski(k3_xboole_0(A_54,k2_xboole_0(B_55,C_56)),k2_xboole_0(B_55,C_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_105,plain,(
    ! [A_54,A_1] : r1_tarski(k3_xboole_0(A_54,A_1),k2_xboole_0(A_1,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_99])).

tff(c_122,plain,(
    ! [A_60,A_61] : r1_tarski(k3_xboole_0(A_60,A_61),A_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_105])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_79,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_83,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(A_23)
      | ~ v1_relat_1(B_24)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_126,plain,(
    ! [A_60,A_61] :
      ( v1_relat_1(k3_xboole_0(A_60,A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_122,c_83])).

tff(c_110,plain,(
    ! [A_54,A_1] : r1_tarski(k3_xboole_0(A_54,A_1),A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_105])).

tff(c_201,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k2_relat_1(A_74),k2_relat_1(B_75))
      | ~ r1_tarski(A_74,B_75)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k2_relat_1(A_69),k2_relat_1(B_70))
      | ~ r1_tarski(A_69,B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_112,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(A_57,k3_xboole_0(B_58,C_59))
      | ~ r1_tarski(A_57,C_59)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_120,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_112,c_30])).

tff(c_129,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_157,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_154,c_129])).

tff(c_163,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4,c_157])).

tff(c_167,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_126,c_163])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_167])).

tff(c_175,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_204,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_201,c_175])).

tff(c_210,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110,c_204])).

tff(c_214,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_126,c_210])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:48:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.24  
% 2.37/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.24  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.37/1.24  
% 2.37/1.24  %Foreground sorts:
% 2.37/1.24  
% 2.37/1.24  
% 2.37/1.24  %Background operators:
% 2.37/1.24  
% 2.37/1.24  
% 2.37/1.24  %Foreground operators:
% 2.37/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.37/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.37/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.37/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.37/1.24  
% 2.37/1.25  tff(f_77, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 2.37/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.37/1.25  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.37/1.25  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.37/1.25  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.37/1.25  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.37/1.26  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.37/1.26  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.37/1.26  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.37/1.26  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.37/1.26  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.37/1.26  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k3_xboole_0(A_8, C_10))=k3_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.37/1.26  tff(c_10, plain, (![A_11, B_12, C_13]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13)), k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.26  tff(c_99, plain, (![A_54, B_55, C_56]: (r1_tarski(k3_xboole_0(A_54, k2_xboole_0(B_55, C_56)), k2_xboole_0(B_55, C_56)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.37/1.26  tff(c_105, plain, (![A_54, A_1]: (r1_tarski(k3_xboole_0(A_54, A_1), k2_xboole_0(A_1, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_99])).
% 2.37/1.26  tff(c_122, plain, (![A_60, A_61]: (r1_tarski(k3_xboole_0(A_60, A_61), A_61))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_105])).
% 2.37/1.26  tff(c_22, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.37/1.26  tff(c_79, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.37/1.26  tff(c_83, plain, (![A_23, B_24]: (v1_relat_1(A_23) | ~v1_relat_1(B_24) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_22, c_79])).
% 2.37/1.26  tff(c_126, plain, (![A_60, A_61]: (v1_relat_1(k3_xboole_0(A_60, A_61)) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_122, c_83])).
% 2.37/1.26  tff(c_110, plain, (![A_54, A_1]: (r1_tarski(k3_xboole_0(A_54, A_1), A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_105])).
% 2.37/1.26  tff(c_201, plain, (![A_74, B_75]: (r1_tarski(k2_relat_1(A_74), k2_relat_1(B_75)) | ~r1_tarski(A_74, B_75) | ~v1_relat_1(B_75) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.37/1.26  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.37/1.26  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.37/1.26  tff(c_154, plain, (![A_69, B_70]: (r1_tarski(k2_relat_1(A_69), k2_relat_1(B_70)) | ~r1_tarski(A_69, B_70) | ~v1_relat_1(B_70) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.37/1.26  tff(c_112, plain, (![A_57, B_58, C_59]: (r1_tarski(A_57, k3_xboole_0(B_58, C_59)) | ~r1_tarski(A_57, C_59) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.37/1.26  tff(c_30, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.37/1.26  tff(c_120, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_112, c_30])).
% 2.37/1.26  tff(c_129, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_120])).
% 2.37/1.26  tff(c_157, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_154, c_129])).
% 2.37/1.26  tff(c_163, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4, c_157])).
% 2.37/1.26  tff(c_167, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_126, c_163])).
% 2.37/1.26  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_167])).
% 2.37/1.26  tff(c_175, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_120])).
% 2.37/1.26  tff(c_204, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_201, c_175])).
% 2.37/1.26  tff(c_210, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_110, c_204])).
% 2.37/1.26  tff(c_214, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_126, c_210])).
% 2.37/1.26  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_214])).
% 2.37/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.26  
% 2.37/1.26  Inference rules
% 2.37/1.26  ----------------------
% 2.37/1.26  #Ref     : 0
% 2.37/1.26  #Sup     : 37
% 2.37/1.26  #Fact    : 0
% 2.37/1.26  #Define  : 0
% 2.37/1.26  #Split   : 2
% 2.37/1.26  #Chain   : 0
% 2.37/1.26  #Close   : 0
% 2.37/1.26  
% 2.37/1.26  Ordering : KBO
% 2.37/1.26  
% 2.37/1.26  Simplification rules
% 2.37/1.26  ----------------------
% 2.37/1.26  #Subsume      : 2
% 2.37/1.26  #Demod        : 15
% 2.37/1.26  #Tautology    : 21
% 2.37/1.26  #SimpNegUnit  : 0
% 2.37/1.26  #BackRed      : 0
% 2.37/1.26  
% 2.37/1.26  #Partial instantiations: 0
% 2.37/1.26  #Strategies tried      : 1
% 2.37/1.26  
% 2.37/1.26  Timing (in seconds)
% 2.37/1.26  ----------------------
% 2.37/1.26  Preprocessing        : 0.30
% 2.37/1.26  Parsing              : 0.16
% 2.37/1.26  CNF conversion       : 0.02
% 2.37/1.26  Main loop            : 0.18
% 2.37/1.26  Inferencing          : 0.07
% 2.37/1.26  Reduction            : 0.05
% 2.37/1.26  Demodulation         : 0.04
% 2.37/1.26  BG Simplification    : 0.01
% 2.37/1.26  Subsumption          : 0.03
% 2.37/1.26  Abstraction          : 0.01
% 2.37/1.26  MUC search           : 0.00
% 2.37/1.26  Cooper               : 0.00
% 2.37/1.26  Total                : 0.51
% 2.37/1.26  Index Insertion      : 0.00
% 2.37/1.26  Index Deletion       : 0.00
% 2.37/1.26  Index Matching       : 0.00
% 2.37/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
