%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:33 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   59 (  63 expanded)
%              Number of leaves         :   35 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  56 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_48,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_60,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_69,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_43,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_20,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_124,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_115])).

tff(c_128,plain,(
    ! [A_46] : k4_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_124])).

tff(c_22,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_15,B_16] : m1_subset_1(k6_subset_1(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_15,B_16] : m1_subset_1(k4_xboole_0(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18])).

tff(c_134,plain,(
    ! [A_46] : m1_subset_1(A_46,k1_zfmisc_1(A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_36])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,B_23)
      | v1_xboole_0(B_23)
      | ~ m1_subset_1(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_24] : k9_setfam_1(A_24) = k1_zfmisc_1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [A_26] : k2_yellow_1(k9_setfam_1(A_26)) = k3_yellow_1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_35,plain,(
    ! [A_26] : k2_yellow_1(k1_zfmisc_1(A_26)) = k3_yellow_1(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_16,plain,(
    ! [A_14] : k3_tarski(k1_zfmisc_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_155,plain,(
    ! [A_53] :
      ( k4_yellow_0(k2_yellow_1(A_53)) = k3_tarski(A_53)
      | ~ r2_hidden(k3_tarski(A_53),A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_162,plain,(
    ! [A_14] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_14))) = k3_tarski(k1_zfmisc_1(A_14))
      | ~ r2_hidden(A_14,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_155])).

tff(c_164,plain,(
    ! [A_14] :
      ( k4_yellow_0(k3_yellow_1(A_14)) = A_14
      | ~ r2_hidden(A_14,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_16,c_162])).

tff(c_166,plain,(
    ! [A_54] :
      ( k4_yellow_0(k3_yellow_1(A_54)) = A_54
      | ~ r2_hidden(A_54,k1_zfmisc_1(A_54)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_164])).

tff(c_170,plain,(
    ! [A_22] :
      ( k4_yellow_0(k3_yellow_1(A_22)) = A_22
      | v1_xboole_0(k1_zfmisc_1(A_22))
      | ~ m1_subset_1(A_22,k1_zfmisc_1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_26,c_166])).

tff(c_173,plain,(
    ! [A_22] :
      ( k4_yellow_0(k3_yellow_1(A_22)) = A_22
      | v1_xboole_0(k1_zfmisc_1(A_22)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_170])).

tff(c_174,plain,(
    ! [A_22] : k4_yellow_0(k3_yellow_1(A_22)) = A_22 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_173])).

tff(c_34,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n003.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 09:44:12 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.16  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2
% 1.73/1.16  
% 1.73/1.16  %Foreground sorts:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Background operators:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Foreground operators:
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.16  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.73/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.73/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.73/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.16  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.73/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.73/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.73/1.16  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.73/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.73/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.16  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.73/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.73/1.16  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.73/1.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.73/1.16  
% 1.73/1.17  tff(f_48, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.73/1.17  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.73/1.17  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.73/1.17  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.73/1.17  tff(f_50, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.73/1.17  tff(f_45, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 1.73/1.17  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.73/1.17  tff(f_60, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.73/1.17  tff(f_69, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.73/1.17  tff(f_43, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.73/1.17  tff(f_67, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 1.73/1.17  tff(f_72, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_1)).
% 1.73/1.17  tff(c_20, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.17  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.73/1.17  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.17  tff(c_115, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.17  tff(c_124, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_115])).
% 1.73/1.17  tff(c_128, plain, (![A_46]: (k4_xboole_0(A_46, k1_xboole_0)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_124])).
% 1.73/1.17  tff(c_22, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.17  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k6_subset_1(A_15, B_16), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.73/1.17  tff(c_36, plain, (![A_15, B_16]: (m1_subset_1(k4_xboole_0(A_15, B_16), k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18])).
% 1.73/1.17  tff(c_134, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_36])).
% 1.73/1.17  tff(c_26, plain, (![A_22, B_23]: (r2_hidden(A_22, B_23) | v1_xboole_0(B_23) | ~m1_subset_1(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.73/1.17  tff(c_28, plain, (![A_24]: (k9_setfam_1(A_24)=k1_zfmisc_1(A_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.73/1.17  tff(c_32, plain, (![A_26]: (k2_yellow_1(k9_setfam_1(A_26))=k3_yellow_1(A_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.73/1.17  tff(c_35, plain, (![A_26]: (k2_yellow_1(k1_zfmisc_1(A_26))=k3_yellow_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 1.73/1.17  tff(c_16, plain, (![A_14]: (k3_tarski(k1_zfmisc_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.73/1.17  tff(c_155, plain, (![A_53]: (k4_yellow_0(k2_yellow_1(A_53))=k3_tarski(A_53) | ~r2_hidden(k3_tarski(A_53), A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.73/1.17  tff(c_162, plain, (![A_14]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_14)))=k3_tarski(k1_zfmisc_1(A_14)) | ~r2_hidden(A_14, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_155])).
% 1.73/1.17  tff(c_164, plain, (![A_14]: (k4_yellow_0(k3_yellow_1(A_14))=A_14 | ~r2_hidden(A_14, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_16, c_162])).
% 1.73/1.17  tff(c_166, plain, (![A_54]: (k4_yellow_0(k3_yellow_1(A_54))=A_54 | ~r2_hidden(A_54, k1_zfmisc_1(A_54)))), inference(negUnitSimplification, [status(thm)], [c_20, c_164])).
% 1.73/1.17  tff(c_170, plain, (![A_22]: (k4_yellow_0(k3_yellow_1(A_22))=A_22 | v1_xboole_0(k1_zfmisc_1(A_22)) | ~m1_subset_1(A_22, k1_zfmisc_1(A_22)))), inference(resolution, [status(thm)], [c_26, c_166])).
% 1.73/1.17  tff(c_173, plain, (![A_22]: (k4_yellow_0(k3_yellow_1(A_22))=A_22 | v1_xboole_0(k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_170])).
% 1.73/1.17  tff(c_174, plain, (![A_22]: (k4_yellow_0(k3_yellow_1(A_22))=A_22)), inference(negUnitSimplification, [status(thm)], [c_20, c_173])).
% 1.73/1.17  tff(c_34, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.73/1.17  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_34])).
% 1.73/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.17  
% 1.73/1.17  Inference rules
% 1.73/1.17  ----------------------
% 1.73/1.17  #Ref     : 0
% 1.73/1.17  #Sup     : 29
% 1.73/1.17  #Fact    : 0
% 1.73/1.17  #Define  : 0
% 1.73/1.17  #Split   : 0
% 1.73/1.17  #Chain   : 0
% 1.73/1.17  #Close   : 0
% 1.73/1.17  
% 1.73/1.17  Ordering : KBO
% 1.73/1.17  
% 1.73/1.17  Simplification rules
% 1.73/1.17  ----------------------
% 1.73/1.17  #Subsume      : 0
% 1.73/1.17  #Demod        : 8
% 1.73/1.17  #Tautology    : 25
% 1.73/1.17  #SimpNegUnit  : 2
% 1.73/1.17  #BackRed      : 1
% 1.73/1.17  
% 1.73/1.17  #Partial instantiations: 0
% 1.73/1.17  #Strategies tried      : 1
% 1.73/1.17  
% 1.73/1.17  Timing (in seconds)
% 1.73/1.17  ----------------------
% 1.73/1.18  Preprocessing        : 0.32
% 1.73/1.18  Parsing              : 0.17
% 1.73/1.18  CNF conversion       : 0.02
% 1.73/1.18  Main loop            : 0.13
% 1.73/1.18  Inferencing          : 0.06
% 1.73/1.18  Reduction            : 0.04
% 1.73/1.18  Demodulation         : 0.03
% 1.73/1.18  BG Simplification    : 0.01
% 1.73/1.18  Subsumption          : 0.01
% 1.73/1.18  Abstraction          : 0.01
% 1.73/1.18  MUC search           : 0.00
% 1.73/1.18  Cooper               : 0.00
% 1.73/1.18  Total                : 0.48
% 1.73/1.18  Index Insertion      : 0.00
% 1.73/1.18  Index Deletion       : 0.00
% 1.73/1.18  Index Matching       : 0.00
% 1.73/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
