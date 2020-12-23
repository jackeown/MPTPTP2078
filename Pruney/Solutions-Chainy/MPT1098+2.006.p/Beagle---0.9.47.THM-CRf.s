%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:27 EST 2020

% Result     : Theorem 6.15s
% Output     : CNFRefutation 6.51s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :   68 ( 135 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_finset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( v1_finset_1(A)
          & r1_tarski(A,k2_zfmisc_1(B,C))
          & ! [D] :
              ~ ( v1_finset_1(D)
                & r1_tarski(D,B)
                & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_26,plain,(
    v1_finset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski('#skF_1'(A_11,B_12,C_13),B_12)
      | ~ r1_tarski(A_11,k2_zfmisc_1(B_12,C_13))
      | ~ v1_finset_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_412,plain,(
    ! [A_52,B_53,C_54] :
      ( v1_finset_1('#skF_1'(A_52,B_53,C_54))
      | ~ r1_tarski(A_52,k2_zfmisc_1(B_53,C_54))
      | ~ v1_finset_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_418,plain,
    ( v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_412])).

tff(c_422,plain,(
    v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_418])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(A_11,k2_zfmisc_1('#skF_1'(A_11,B_12,C_13),'#skF_2'(A_11,B_12,C_13)))
      | ~ r1_tarski(A_11,k2_zfmisc_1(B_12,C_13))
      | ~ v1_finset_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1785,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_tarski('#skF_2'(A_99,B_100,C_101),C_101)
      | ~ r1_tarski(A_99,k2_zfmisc_1(B_100,C_101))
      | ~ v1_finset_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1802,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_xboole_0('#skF_2'(A_99,B_100,C_101),C_101) = C_101
      | ~ r1_tarski(A_99,k2_zfmisc_1(B_100,C_101))
      | ~ v1_finset_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_1785,c_6])).

tff(c_3482,plain,(
    ! [C_149,A_150,B_151] :
      ( k2_xboole_0(C_149,'#skF_2'(A_150,B_151,C_149)) = C_149
      | ~ r1_tarski(A_150,k2_zfmisc_1(B_151,C_149))
      | ~ v1_finset_1(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1802])).

tff(c_3514,plain,
    ( k2_xboole_0('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5'
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_3482])).

tff(c_3525,plain,(
    k2_xboole_0('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3514])).

tff(c_946,plain,(
    ! [C_78,A_79,B_80] : k2_xboole_0(k2_zfmisc_1(C_78,A_79),k2_zfmisc_1(C_78,B_80)) = k2_zfmisc_1(C_78,k2_xboole_0(A_79,B_80)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_987,plain,(
    ! [A_3,C_78,A_79,B_80] :
      ( r1_tarski(A_3,k2_zfmisc_1(C_78,k2_xboole_0(A_79,B_80)))
      | ~ r1_tarski(A_3,k2_zfmisc_1(C_78,B_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_4])).

tff(c_4769,plain,(
    ! [A_207,C_208] :
      ( r1_tarski(A_207,k2_zfmisc_1(C_208,'#skF_5'))
      | ~ r1_tarski(A_207,k2_zfmisc_1(C_208,'#skF_2'('#skF_3','#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3525,c_987])).

tff(c_4792,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_5'))
    | ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_4769])).

tff(c_4815,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_4792])).

tff(c_22,plain,(
    ! [D_17] :
      ( ~ r1_tarski('#skF_3',k2_zfmisc_1(D_17,'#skF_5'))
      | ~ r1_tarski(D_17,'#skF_4')
      | ~ v1_finset_1(D_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4841,plain,
    ( ~ r1_tarski('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ v1_finset_1('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4815,c_22])).

tff(c_4865,plain,(
    ~ r1_tarski('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_4841])).

tff(c_4869,plain,
    ( ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_4865])).

tff(c_4873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_4869])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.15/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.29  
% 6.15/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.30  %$ r1_tarski > v1_finset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 6.15/2.30  
% 6.15/2.30  %Foreground sorts:
% 6.15/2.30  
% 6.15/2.30  
% 6.15/2.30  %Background operators:
% 6.15/2.30  
% 6.15/2.30  
% 6.15/2.30  %Foreground operators:
% 6.15/2.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.15/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.15/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.15/2.30  tff('#skF_5', type, '#skF_5': $i).
% 6.15/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.15/2.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.15/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.15/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.15/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.15/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.15/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.15/2.30  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 6.15/2.30  
% 6.51/2.31  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D]: ~((v1_finset_1(D) & r1_tarski(D, B)) & r1_tarski(A, k2_zfmisc_1(D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_finset_1)).
% 6.51/2.31  tff(f_56, axiom, (![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D, E]: ~((((v1_finset_1(D) & r1_tarski(D, B)) & v1_finset_1(E)) & r1_tarski(E, C)) & r1_tarski(A, k2_zfmisc_1(D, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_finset_1)).
% 6.51/2.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.51/2.31  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.51/2.31  tff(f_39, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 6.51/2.31  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 6.51/2.31  tff(c_26, plain, (v1_finset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.51/2.31  tff(c_24, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.51/2.31  tff(c_18, plain, (![A_11, B_12, C_13]: (r1_tarski('#skF_1'(A_11, B_12, C_13), B_12) | ~r1_tarski(A_11, k2_zfmisc_1(B_12, C_13)) | ~v1_finset_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.51/2.31  tff(c_412, plain, (![A_52, B_53, C_54]: (v1_finset_1('#skF_1'(A_52, B_53, C_54)) | ~r1_tarski(A_52, k2_zfmisc_1(B_53, C_54)) | ~v1_finset_1(A_52))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.51/2.31  tff(c_418, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_412])).
% 6.51/2.31  tff(c_422, plain, (v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_418])).
% 6.51/2.31  tff(c_12, plain, (![A_11, B_12, C_13]: (r1_tarski(A_11, k2_zfmisc_1('#skF_1'(A_11, B_12, C_13), '#skF_2'(A_11, B_12, C_13))) | ~r1_tarski(A_11, k2_zfmisc_1(B_12, C_13)) | ~v1_finset_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.51/2.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.51/2.31  tff(c_1785, plain, (![A_99, B_100, C_101]: (r1_tarski('#skF_2'(A_99, B_100, C_101), C_101) | ~r1_tarski(A_99, k2_zfmisc_1(B_100, C_101)) | ~v1_finset_1(A_99))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.51/2.31  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.51/2.31  tff(c_1802, plain, (![A_99, B_100, C_101]: (k2_xboole_0('#skF_2'(A_99, B_100, C_101), C_101)=C_101 | ~r1_tarski(A_99, k2_zfmisc_1(B_100, C_101)) | ~v1_finset_1(A_99))), inference(resolution, [status(thm)], [c_1785, c_6])).
% 6.51/2.31  tff(c_3482, plain, (![C_149, A_150, B_151]: (k2_xboole_0(C_149, '#skF_2'(A_150, B_151, C_149))=C_149 | ~r1_tarski(A_150, k2_zfmisc_1(B_151, C_149)) | ~v1_finset_1(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1802])).
% 6.51/2.31  tff(c_3514, plain, (k2_xboole_0('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5' | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_3482])).
% 6.51/2.31  tff(c_3525, plain, (k2_xboole_0('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3514])).
% 6.51/2.31  tff(c_946, plain, (![C_78, A_79, B_80]: (k2_xboole_0(k2_zfmisc_1(C_78, A_79), k2_zfmisc_1(C_78, B_80))=k2_zfmisc_1(C_78, k2_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.51/2.31  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.51/2.31  tff(c_987, plain, (![A_3, C_78, A_79, B_80]: (r1_tarski(A_3, k2_zfmisc_1(C_78, k2_xboole_0(A_79, B_80))) | ~r1_tarski(A_3, k2_zfmisc_1(C_78, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_946, c_4])).
% 6.51/2.31  tff(c_4769, plain, (![A_207, C_208]: (r1_tarski(A_207, k2_zfmisc_1(C_208, '#skF_5')) | ~r1_tarski(A_207, k2_zfmisc_1(C_208, '#skF_2'('#skF_3', '#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_3525, c_987])).
% 6.51/2.31  tff(c_4792, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')) | ~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_4769])).
% 6.51/2.31  tff(c_4815, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_4792])).
% 6.51/2.31  tff(c_22, plain, (![D_17]: (~r1_tarski('#skF_3', k2_zfmisc_1(D_17, '#skF_5')) | ~r1_tarski(D_17, '#skF_4') | ~v1_finset_1(D_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.51/2.31  tff(c_4841, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~v1_finset_1('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4815, c_22])).
% 6.51/2.31  tff(c_4865, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_422, c_4841])).
% 6.51/2.31  tff(c_4869, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5')) | ~v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_4865])).
% 6.51/2.31  tff(c_4873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_4869])).
% 6.51/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.51/2.31  
% 6.51/2.31  Inference rules
% 6.51/2.31  ----------------------
% 6.51/2.31  #Ref     : 0
% 6.51/2.31  #Sup     : 1370
% 6.51/2.31  #Fact    : 0
% 6.51/2.31  #Define  : 0
% 6.51/2.31  #Split   : 4
% 6.51/2.31  #Chain   : 0
% 6.51/2.31  #Close   : 0
% 6.51/2.31  
% 6.51/2.31  Ordering : KBO
% 6.51/2.31  
% 6.51/2.31  Simplification rules
% 6.51/2.31  ----------------------
% 6.51/2.31  #Subsume      : 282
% 6.51/2.31  #Demod        : 280
% 6.51/2.31  #Tautology    : 184
% 6.51/2.31  #SimpNegUnit  : 0
% 6.51/2.31  #BackRed      : 0
% 6.51/2.31  
% 6.51/2.31  #Partial instantiations: 0
% 6.51/2.31  #Strategies tried      : 1
% 6.51/2.31  
% 6.51/2.31  Timing (in seconds)
% 6.51/2.31  ----------------------
% 6.51/2.31  Preprocessing        : 0.29
% 6.51/2.31  Parsing              : 0.16
% 6.51/2.31  CNF conversion       : 0.02
% 6.51/2.31  Main loop            : 1.25
% 6.51/2.31  Inferencing          : 0.38
% 6.51/2.31  Reduction            : 0.47
% 6.51/2.31  Demodulation         : 0.38
% 6.51/2.31  BG Simplification    : 0.05
% 6.51/2.31  Subsumption          : 0.26
% 6.51/2.31  Abstraction          : 0.06
% 6.51/2.31  MUC search           : 0.00
% 6.51/2.31  Cooper               : 0.00
% 6.51/2.31  Total                : 1.57
% 6.51/2.31  Index Insertion      : 0.00
% 6.51/2.31  Index Deletion       : 0.00
% 6.51/2.31  Index Matching       : 0.00
% 6.51/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
