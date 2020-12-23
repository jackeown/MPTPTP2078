%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:54 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :   54 (  71 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 (  89 expanded)
%              Number of equality atoms :   34 (  46 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_236,plain,(
    ! [A_44,B_45] :
      ( k3_subset_1(A_44,k3_subset_1(A_44,B_45)) = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_245,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_236])).

tff(c_194,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k3_subset_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_202,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_213,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_8])).

tff(c_231,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k3_subset_1(A_42,B_43),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k3_subset_1(A_13,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4059,plain,(
    ! [A_102,B_103] :
      ( k4_xboole_0(A_102,k3_subset_1(A_102,B_103)) = k3_subset_1(A_102,k3_subset_1(A_102,B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(resolution,[status(thm)],[c_231,c_12])).

tff(c_4065,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_4059])).

tff(c_4070,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_213,c_4065])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4194,plain,(
    ! [C_12] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_12)) = k4_xboole_0('#skF_2',C_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_4070,c_10])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_201,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_194])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [A_34,B_35,C_36] : k4_xboole_0(k3_xboole_0(A_34,B_35),C_36) = k3_xboole_0(A_34,k4_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_615,plain,(
    ! [A_59,B_60,C_61] : k4_xboole_0(k3_xboole_0(A_59,B_60),C_61) = k3_xboole_0(B_60,k4_xboole_0(A_59,C_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_118])).

tff(c_1997,plain,(
    ! [B_85,A_86,C_87] : k3_xboole_0(B_85,k4_xboole_0(A_86,C_87)) = k3_xboole_0(A_86,k4_xboole_0(B_85,C_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_10])).

tff(c_2269,plain,(
    ! [A_86] : k3_xboole_0(A_86,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1',k4_xboole_0(A_86,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_1997])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k3_subset_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_680,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,C_64) = k3_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6778,plain,(
    ! [A_117,B_118,B_119] :
      ( k9_subset_1(A_117,B_118,k3_subset_1(A_117,B_119)) = k3_xboole_0(B_118,k3_subset_1(A_117,B_119))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_117)) ) ),
    inference(resolution,[status(thm)],[c_14,c_680])).

tff(c_6786,plain,(
    ! [B_118] : k9_subset_1('#skF_1',B_118,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0(B_118,k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_6778])).

tff(c_571,plain,(
    ! [A_54,B_55,C_56] :
      ( k7_subset_1(A_54,B_55,C_56) = k4_xboole_0(B_55,C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_580,plain,(
    ! [C_56] : k7_subset_1('#skF_1','#skF_2',C_56) = k4_xboole_0('#skF_2',C_56) ),
    inference(resolution,[status(thm)],[c_26,c_571])).

tff(c_22,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k7_subset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_590,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_22])).

tff(c_7121,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6786,c_590])).

tff(c_7124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4194,c_2269,c_7121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.59/2.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.93  
% 7.59/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.94  %$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.59/2.94  
% 7.59/2.94  %Foreground sorts:
% 7.59/2.94  
% 7.59/2.94  
% 7.59/2.94  %Background operators:
% 7.59/2.94  
% 7.59/2.94  
% 7.59/2.94  %Foreground operators:
% 7.59/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.59/2.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.59/2.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.59/2.94  tff('#skF_2', type, '#skF_2': $i).
% 7.59/2.94  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.59/2.94  tff('#skF_3', type, '#skF_3': $i).
% 7.59/2.94  tff('#skF_1', type, '#skF_1': $i).
% 7.59/2.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.59/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.59/2.94  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.59/2.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.59/2.94  
% 7.59/2.95  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 7.59/2.95  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.59/2.95  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.59/2.95  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.59/2.95  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.59/2.95  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.59/2.95  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.59/2.95  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.59/2.95  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.59/2.95  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.59/2.95  tff(c_236, plain, (![A_44, B_45]: (k3_subset_1(A_44, k3_subset_1(A_44, B_45))=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.59/2.95  tff(c_245, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_236])).
% 7.59/2.95  tff(c_194, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k3_subset_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.59/2.95  tff(c_202, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_194])).
% 7.59/2.95  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.59/2.95  tff(c_213, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_202, c_8])).
% 7.59/2.95  tff(c_231, plain, (![A_42, B_43]: (m1_subset_1(k3_subset_1(A_42, B_43), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.59/2.95  tff(c_12, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k3_subset_1(A_13, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.59/2.95  tff(c_4059, plain, (![A_102, B_103]: (k4_xboole_0(A_102, k3_subset_1(A_102, B_103))=k3_subset_1(A_102, k3_subset_1(A_102, B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(resolution, [status(thm)], [c_231, c_12])).
% 7.59/2.95  tff(c_4065, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_4059])).
% 7.59/2.95  tff(c_4070, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_245, c_213, c_4065])).
% 7.59/2.95  tff(c_10, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.59/2.95  tff(c_4194, plain, (![C_12]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_12))=k4_xboole_0('#skF_2', C_12))), inference(superposition, [status(thm), theory('equality')], [c_4070, c_10])).
% 7.59/2.95  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.59/2.95  tff(c_201, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_194])).
% 7.59/2.95  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.59/2.95  tff(c_118, plain, (![A_34, B_35, C_36]: (k4_xboole_0(k3_xboole_0(A_34, B_35), C_36)=k3_xboole_0(A_34, k4_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.59/2.95  tff(c_615, plain, (![A_59, B_60, C_61]: (k4_xboole_0(k3_xboole_0(A_59, B_60), C_61)=k3_xboole_0(B_60, k4_xboole_0(A_59, C_61)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_118])).
% 7.59/2.95  tff(c_1997, plain, (![B_85, A_86, C_87]: (k3_xboole_0(B_85, k4_xboole_0(A_86, C_87))=k3_xboole_0(A_86, k4_xboole_0(B_85, C_87)))), inference(superposition, [status(thm), theory('equality')], [c_615, c_10])).
% 7.59/2.95  tff(c_2269, plain, (![A_86]: (k3_xboole_0(A_86, k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', k4_xboole_0(A_86, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_201, c_1997])).
% 7.59/2.95  tff(c_14, plain, (![A_15, B_16]: (m1_subset_1(k3_subset_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.59/2.95  tff(c_680, plain, (![A_62, B_63, C_64]: (k9_subset_1(A_62, B_63, C_64)=k3_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.59/2.95  tff(c_6778, plain, (![A_117, B_118, B_119]: (k9_subset_1(A_117, B_118, k3_subset_1(A_117, B_119))=k3_xboole_0(B_118, k3_subset_1(A_117, B_119)) | ~m1_subset_1(B_119, k1_zfmisc_1(A_117)))), inference(resolution, [status(thm)], [c_14, c_680])).
% 7.59/2.95  tff(c_6786, plain, (![B_118]: (k9_subset_1('#skF_1', B_118, k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0(B_118, k3_subset_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_24, c_6778])).
% 7.59/2.95  tff(c_571, plain, (![A_54, B_55, C_56]: (k7_subset_1(A_54, B_55, C_56)=k4_xboole_0(B_55, C_56) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.59/2.95  tff(c_580, plain, (![C_56]: (k7_subset_1('#skF_1', '#skF_2', C_56)=k4_xboole_0('#skF_2', C_56))), inference(resolution, [status(thm)], [c_26, c_571])).
% 7.59/2.95  tff(c_22, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k7_subset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.59/2.95  tff(c_590, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_22])).
% 7.59/2.95  tff(c_7121, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6786, c_590])).
% 7.59/2.95  tff(c_7124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4194, c_2269, c_7121])).
% 7.59/2.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.95  
% 7.59/2.95  Inference rules
% 7.59/2.95  ----------------------
% 7.59/2.95  #Ref     : 0
% 7.59/2.95  #Sup     : 1864
% 7.59/2.95  #Fact    : 0
% 7.59/2.95  #Define  : 0
% 7.59/2.95  #Split   : 0
% 7.59/2.95  #Chain   : 0
% 7.59/2.95  #Close   : 0
% 7.59/2.95  
% 7.59/2.95  Ordering : KBO
% 7.59/2.95  
% 7.59/2.95  Simplification rules
% 7.59/2.95  ----------------------
% 7.59/2.95  #Subsume      : 151
% 7.59/2.95  #Demod        : 1552
% 7.59/2.95  #Tautology    : 354
% 7.59/2.95  #SimpNegUnit  : 0
% 7.59/2.95  #BackRed      : 8
% 7.59/2.95  
% 7.59/2.95  #Partial instantiations: 0
% 7.59/2.95  #Strategies tried      : 1
% 7.59/2.95  
% 7.59/2.95  Timing (in seconds)
% 7.59/2.95  ----------------------
% 7.59/2.95  Preprocessing        : 0.30
% 7.59/2.95  Parsing              : 0.16
% 7.59/2.95  CNF conversion       : 0.02
% 7.59/2.95  Main loop            : 1.89
% 7.59/2.95  Inferencing          : 0.36
% 7.59/2.95  Reduction            : 1.20
% 7.59/2.95  Demodulation         : 1.10
% 7.59/2.95  BG Simplification    : 0.07
% 7.59/2.95  Subsumption          : 0.19
% 7.59/2.95  Abstraction          : 0.09
% 7.59/2.95  MUC search           : 0.00
% 7.59/2.95  Cooper               : 0.00
% 7.59/2.95  Total                : 2.22
% 7.59/2.95  Index Insertion      : 0.00
% 7.59/2.95  Index Deletion       : 0.00
% 7.59/2.95  Index Matching       : 0.00
% 7.59/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
