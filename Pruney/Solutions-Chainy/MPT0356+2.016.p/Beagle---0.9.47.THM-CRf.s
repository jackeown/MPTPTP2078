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
% DateTime   : Thu Dec  3 09:55:57 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   62 (  71 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 (  98 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_72,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k2_subset_1(A_16),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_16] : m1_subset_1(A_16,k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_12] : k1_subset_1(A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = k2_subset_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_39,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_41,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_39])).

tff(c_30,plain,(
    ! [A_24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_215,plain,(
    ! [A_52,B_53] :
      ( k3_subset_1(A_52,k3_subset_1(A_52,B_53)) = B_53
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_219,plain,(
    ! [A_24] : k3_subset_1(A_24,k3_subset_1(A_24,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_215])).

tff(c_226,plain,(
    ! [A_24] : k3_subset_1(A_24,A_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_219])).

tff(c_368,plain,(
    ! [B_69,C_70,A_71] :
      ( r1_tarski(B_69,C_70)
      | ~ r1_tarski(k3_subset_1(A_71,C_70),k3_subset_1(A_71,B_69))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_383,plain,(
    ! [B_69,A_24] :
      ( r1_tarski(B_69,A_24)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_24,B_69))
      | ~ m1_subset_1(A_24,k1_zfmisc_1(A_24))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_368])).

tff(c_401,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(B_72,A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10,c_383])).

tff(c_417,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_401])).

tff(c_34,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_102,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k3_subset_1(A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_118,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_204,plain,(
    ! [A_51] :
      ( r1_xboole_0(A_51,'#skF_3')
      | ~ r1_tarski(A_51,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_6])).

tff(c_212,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_204])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_231,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_212,c_2])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_119,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_102])).

tff(c_291,plain,(
    ! [A_58,B_59,C_60] :
      ( r1_tarski(A_58,k4_xboole_0(B_59,C_60))
      | ~ r1_xboole_0(A_58,C_60)
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_616,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_82,'#skF_2')
      | ~ r1_tarski(A_82,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_291])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_629,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_616,c_32])).

tff(c_638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_231,c_629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.33  
% 2.55/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.33  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.55/1.33  
% 2.55/1.33  %Foreground sorts:
% 2.55/1.33  
% 2.55/1.33  
% 2.55/1.33  %Background operators:
% 2.55/1.33  
% 2.55/1.33  
% 2.55/1.33  %Foreground operators:
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.55/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.55/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.55/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.33  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.55/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.55/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.33  
% 2.55/1.34  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 2.55/1.34  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.55/1.34  tff(f_55, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.55/1.34  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.55/1.34  tff(f_47, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.55/1.34  tff(f_61, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.55/1.34  tff(f_72, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.55/1.34  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.55/1.34  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.55/1.34  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.55/1.34  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.55/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.55/1.34  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.55/1.34  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.34  tff(c_16, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.34  tff(c_20, plain, (![A_16]: (m1_subset_1(k2_subset_1(A_16), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.34  tff(c_40, plain, (![A_16]: (m1_subset_1(A_16, k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 2.55/1.34  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.34  tff(c_14, plain, (![A_12]: (k1_subset_1(A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.55/1.34  tff(c_24, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=k2_subset_1(A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.34  tff(c_39, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 2.55/1.34  tff(c_41, plain, (![A_19]: (k3_subset_1(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_39])).
% 2.55/1.34  tff(c_30, plain, (![A_24]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.55/1.34  tff(c_215, plain, (![A_52, B_53]: (k3_subset_1(A_52, k3_subset_1(A_52, B_53))=B_53 | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.55/1.34  tff(c_219, plain, (![A_24]: (k3_subset_1(A_24, k3_subset_1(A_24, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_215])).
% 2.55/1.34  tff(c_226, plain, (![A_24]: (k3_subset_1(A_24, A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_41, c_219])).
% 2.55/1.34  tff(c_368, plain, (![B_69, C_70, A_71]: (r1_tarski(B_69, C_70) | ~r1_tarski(k3_subset_1(A_71, C_70), k3_subset_1(A_71, B_69)) | ~m1_subset_1(C_70, k1_zfmisc_1(A_71)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.55/1.34  tff(c_383, plain, (![B_69, A_24]: (r1_tarski(B_69, A_24) | ~r1_tarski(k1_xboole_0, k3_subset_1(A_24, B_69)) | ~m1_subset_1(A_24, k1_zfmisc_1(A_24)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_368])).
% 2.55/1.34  tff(c_401, plain, (![B_72, A_73]: (r1_tarski(B_72, A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10, c_383])).
% 2.55/1.34  tff(c_417, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_401])).
% 2.55/1.34  tff(c_34, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.34  tff(c_102, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k3_subset_1(A_44, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.55/1.34  tff(c_118, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_102])).
% 2.55/1.34  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.55/1.34  tff(c_204, plain, (![A_51]: (r1_xboole_0(A_51, '#skF_3') | ~r1_tarski(A_51, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_118, c_6])).
% 2.55/1.34  tff(c_212, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_204])).
% 2.55/1.34  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.34  tff(c_231, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_212, c_2])).
% 2.55/1.34  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.34  tff(c_119, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_102])).
% 2.55/1.34  tff(c_291, plain, (![A_58, B_59, C_60]: (r1_tarski(A_58, k4_xboole_0(B_59, C_60)) | ~r1_xboole_0(A_58, C_60) | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.34  tff(c_616, plain, (![A_82]: (r1_tarski(A_82, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_82, '#skF_2') | ~r1_tarski(A_82, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_291])).
% 2.55/1.34  tff(c_32, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.34  tff(c_629, plain, (~r1_xboole_0('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_616, c_32])).
% 2.55/1.34  tff(c_638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_417, c_231, c_629])).
% 2.55/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  Inference rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Ref     : 0
% 2.55/1.34  #Sup     : 135
% 2.55/1.34  #Fact    : 0
% 2.55/1.34  #Define  : 0
% 2.55/1.34  #Split   : 2
% 2.55/1.34  #Chain   : 0
% 2.55/1.34  #Close   : 0
% 2.55/1.34  
% 2.55/1.34  Ordering : KBO
% 2.55/1.34  
% 2.55/1.34  Simplification rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Subsume      : 5
% 2.55/1.34  #Demod        : 57
% 2.55/1.34  #Tautology    : 64
% 2.55/1.34  #SimpNegUnit  : 0
% 2.55/1.34  #BackRed      : 2
% 2.55/1.34  
% 2.55/1.34  #Partial instantiations: 0
% 2.55/1.34  #Strategies tried      : 1
% 2.55/1.34  
% 2.55/1.34  Timing (in seconds)
% 2.55/1.34  ----------------------
% 2.55/1.35  Preprocessing        : 0.30
% 2.55/1.35  Parsing              : 0.16
% 2.55/1.35  CNF conversion       : 0.02
% 2.55/1.35  Main loop            : 0.29
% 2.55/1.35  Inferencing          : 0.11
% 2.55/1.35  Reduction            : 0.09
% 2.55/1.35  Demodulation         : 0.07
% 2.55/1.35  BG Simplification    : 0.01
% 2.55/1.35  Subsumption          : 0.05
% 2.55/1.35  Abstraction          : 0.02
% 2.55/1.35  MUC search           : 0.00
% 2.55/1.35  Cooper               : 0.00
% 2.55/1.35  Total                : 0.62
% 2.55/1.35  Index Insertion      : 0.00
% 2.55/1.35  Index Deletion       : 0.00
% 2.55/1.35  Index Matching       : 0.00
% 2.55/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
