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
% DateTime   : Thu Dec  3 10:22:40 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   53 (  69 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k6_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k5_setfam_1(A,k7_setfam_1(A,B)) = k7_subset_1(A,k2_subset_1(A),k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).

tff(c_22,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_92,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k6_setfam_1(A_28,B_29),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k6_setfam_1(A_30,B_31),A_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(resolution,[status(thm)],[c_92,c_16])).

tff(c_112,plain,(
    r1_tarski(k6_setfam_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_101])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k3_subset_1(A_23,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [B_12,A_11] :
      ( k4_xboole_0(B_12,A_11) = k3_subset_1(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_60])).

tff(c_118,plain,(
    k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_112,c_67])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ! [A_34,B_35,C_36] :
      ( k7_subset_1(A_34,B_35,C_36) = k4_xboole_0(B_35,C_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_152,plain,(
    ! [B_38,A_39,C_40] :
      ( k7_subset_1(B_38,A_39,C_40) = k4_xboole_0(A_39,C_40)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(resolution,[status(thm)],[c_18,c_133])).

tff(c_165,plain,(
    ! [B_2,C_40] : k7_subset_1(B_2,B_2,C_40) = k4_xboole_0(B_2,C_40) ),
    inference(resolution,[status(thm)],[c_6,c_152])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k7_subset_1(A_13,k2_subset_1(A_13),k6_setfam_1(A_13,B_14)) = k5_setfam_1(A_13,k7_setfam_1(A_13,B_14))
      | k1_xboole_0 = B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_166,plain,(
    ! [A_41,B_42] :
      ( k7_subset_1(A_41,A_41,k6_setfam_1(A_41,B_42)) = k5_setfam_1(A_41,k7_setfam_1(A_41,B_42))
      | k1_xboole_0 = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20])).

tff(c_174,plain,
    ( k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_166])).

tff(c_179,plain,(
    k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_174])).

tff(c_190,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_165,c_179])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:06:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.27  
% 1.92/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.27  %$ r1_tarski > m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.92/1.27  
% 1.92/1.27  %Foreground sorts:
% 1.92/1.27  
% 1.92/1.27  
% 1.92/1.27  %Background operators:
% 1.92/1.27  
% 1.92/1.27  
% 1.92/1.27  %Foreground operators:
% 1.92/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.27  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 1.92/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.92/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.27  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.92/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.27  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.92/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.27  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 1.92/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.92/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.27  
% 1.92/1.29  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 1.92/1.29  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k6_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_setfam_1)).
% 1.92/1.29  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.92/1.29  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.92/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.92/1.29  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 1.92/1.29  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.92/1.29  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k7_subset_1(A, k2_subset_1(A), k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_setfam_1)).
% 1.92/1.29  tff(c_22, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.29  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.29  tff(c_92, plain, (![A_28, B_29]: (m1_subset_1(k6_setfam_1(A_28, B_29), k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(k1_zfmisc_1(A_28))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.29  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.29  tff(c_101, plain, (![A_30, B_31]: (r1_tarski(k6_setfam_1(A_30, B_31), A_30) | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(resolution, [status(thm)], [c_92, c_16])).
% 1.92/1.29  tff(c_112, plain, (r1_tarski(k6_setfam_1('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_26, c_101])).
% 1.92/1.29  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.29  tff(c_60, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k3_subset_1(A_23, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.29  tff(c_67, plain, (![B_12, A_11]: (k4_xboole_0(B_12, A_11)=k3_subset_1(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(resolution, [status(thm)], [c_18, c_60])).
% 1.92/1.29  tff(c_118, plain, (k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_112, c_67])).
% 1.92/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.29  tff(c_133, plain, (![A_34, B_35, C_36]: (k7_subset_1(A_34, B_35, C_36)=k4_xboole_0(B_35, C_36) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.29  tff(c_152, plain, (![B_38, A_39, C_40]: (k7_subset_1(B_38, A_39, C_40)=k4_xboole_0(A_39, C_40) | ~r1_tarski(A_39, B_38))), inference(resolution, [status(thm)], [c_18, c_133])).
% 1.92/1.29  tff(c_165, plain, (![B_2, C_40]: (k7_subset_1(B_2, B_2, C_40)=k4_xboole_0(B_2, C_40))), inference(resolution, [status(thm)], [c_6, c_152])).
% 1.92/1.29  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.29  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.29  tff(c_20, plain, (![A_13, B_14]: (k7_subset_1(A_13, k2_subset_1(A_13), k6_setfam_1(A_13, B_14))=k5_setfam_1(A_13, k7_setfam_1(A_13, B_14)) | k1_xboole_0=B_14 | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.92/1.29  tff(c_166, plain, (![A_41, B_42]: (k7_subset_1(A_41, A_41, k6_setfam_1(A_41, B_42))=k5_setfam_1(A_41, k7_setfam_1(A_41, B_42)) | k1_xboole_0=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20])).
% 1.92/1.29  tff(c_174, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_166])).
% 1.92/1.29  tff(c_179, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_174])).
% 1.92/1.29  tff(c_190, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_165, c_179])).
% 1.92/1.29  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_190])).
% 1.92/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.29  
% 1.92/1.29  Inference rules
% 1.92/1.29  ----------------------
% 1.92/1.29  #Ref     : 0
% 1.92/1.29  #Sup     : 39
% 1.92/1.29  #Fact    : 0
% 1.92/1.29  #Define  : 0
% 1.92/1.29  #Split   : 2
% 1.92/1.29  #Chain   : 0
% 1.92/1.29  #Close   : 0
% 1.92/1.29  
% 1.92/1.29  Ordering : KBO
% 1.92/1.29  
% 1.92/1.29  Simplification rules
% 1.92/1.29  ----------------------
% 1.92/1.29  #Subsume      : 0
% 1.92/1.29  #Demod        : 8
% 1.92/1.29  #Tautology    : 17
% 1.92/1.29  #SimpNegUnit  : 2
% 1.92/1.29  #BackRed      : 1
% 1.92/1.29  
% 1.92/1.29  #Partial instantiations: 0
% 1.92/1.29  #Strategies tried      : 1
% 1.92/1.29  
% 1.92/1.29  Timing (in seconds)
% 1.92/1.29  ----------------------
% 1.92/1.29  Preprocessing        : 0.31
% 1.92/1.29  Parsing              : 0.17
% 1.92/1.29  CNF conversion       : 0.02
% 1.92/1.29  Main loop            : 0.15
% 1.92/1.29  Inferencing          : 0.05
% 1.92/1.29  Reduction            : 0.05
% 1.92/1.29  Demodulation         : 0.03
% 1.92/1.29  BG Simplification    : 0.01
% 1.92/1.29  Subsumption          : 0.03
% 1.92/1.29  Abstraction          : 0.01
% 1.92/1.29  MUC search           : 0.00
% 1.92/1.29  Cooper               : 0.00
% 1.92/1.29  Total                : 0.49
% 1.92/1.29  Index Insertion      : 0.00
% 1.92/1.29  Index Deletion       : 0.00
% 1.92/1.29  Index Matching       : 0.00
% 1.92/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
