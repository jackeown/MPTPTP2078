%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:41 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 130 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_27,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_24,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_24])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k3_subset_1(A_23,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_44])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,k4_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_28] :
      ( r1_xboole_0(A_28,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_28,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_4])).

tff(c_93,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_27])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_93])).

tff(c_98,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    ! [A_29,B_30] :
      ( k3_subset_1(A_29,k3_subset_1(A_29,B_30)) = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_102])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k3_subset_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_129,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k3_subset_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_221,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,k3_subset_1(A_44,B_45)) = k3_subset_1(A_44,k3_subset_1(A_44,B_45))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_227,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_221])).

tff(c_232,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_227])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_255,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_2])).

tff(c_100,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_24])).

tff(c_107,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_225,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_221])).

tff(c_230,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_225])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,k4_xboole_0(B_7,C_8))
      | ~ r1_xboole_0(A_6,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_331,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,'#skF_3')
      | ~ r1_xboole_0(A_52,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_52,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_6])).

tff(c_337,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_331])).

tff(c_341,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_337])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.43  
% 2.19/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.44  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.44  
% 2.19/1.44  %Foreground sorts:
% 2.19/1.44  
% 2.19/1.44  
% 2.19/1.44  %Background operators:
% 2.19/1.44  
% 2.19/1.44  
% 2.19/1.44  %Foreground operators:
% 2.19/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.19/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.44  
% 2.19/1.45  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 2.19/1.45  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.19/1.45  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.19/1.45  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.19/1.45  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.19/1.45  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.19/1.45  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.19/1.45  tff(c_18, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.45  tff(c_27, plain, (~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_18])).
% 2.19/1.45  tff(c_24, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.45  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_27, c_24])).
% 2.19/1.45  tff(c_14, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.45  tff(c_44, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k3_subset_1(A_23, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.45  tff(c_51, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_44])).
% 2.19/1.45  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, k4_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.45  tff(c_90, plain, (![A_28]: (r1_xboole_0(A_28, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_28, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_4])).
% 2.19/1.45  tff(c_93, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_90, c_27])).
% 2.19/1.45  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_93])).
% 2.19/1.45  tff(c_98, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 2.19/1.45  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.45  tff(c_102, plain, (![A_29, B_30]: (k3_subset_1(A_29, k3_subset_1(A_29, B_30))=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.45  tff(c_108, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_16, c_102])).
% 2.19/1.45  tff(c_10, plain, (![A_11, B_12]: (m1_subset_1(k3_subset_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.19/1.45  tff(c_129, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k3_subset_1(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.45  tff(c_221, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k3_subset_1(A_44, B_45))=k3_subset_1(A_44, k3_subset_1(A_44, B_45)) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_10, c_129])).
% 2.19/1.45  tff(c_227, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_221])).
% 2.19/1.45  tff(c_232, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_227])).
% 2.19/1.45  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.45  tff(c_255, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_232, c_2])).
% 2.19/1.45  tff(c_100, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_98, c_24])).
% 2.19/1.45  tff(c_107, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_14, c_102])).
% 2.19/1.45  tff(c_225, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_221])).
% 2.19/1.45  tff(c_230, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_225])).
% 2.19/1.45  tff(c_6, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, k4_xboole_0(B_7, C_8)) | ~r1_xboole_0(A_6, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.45  tff(c_331, plain, (![A_52]: (r1_tarski(A_52, '#skF_3') | ~r1_xboole_0(A_52, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_52, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_6])).
% 2.19/1.45  tff(c_337, plain, (r1_tarski('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_100, c_331])).
% 2.19/1.45  tff(c_341, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_337])).
% 2.19/1.45  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_341])).
% 2.19/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.45  
% 2.19/1.45  Inference rules
% 2.19/1.45  ----------------------
% 2.19/1.45  #Ref     : 0
% 2.19/1.45  #Sup     : 86
% 2.19/1.45  #Fact    : 0
% 2.19/1.45  #Define  : 0
% 2.19/1.45  #Split   : 1
% 2.19/1.45  #Chain   : 0
% 2.19/1.45  #Close   : 0
% 2.19/1.45  
% 2.19/1.45  Ordering : KBO
% 2.19/1.45  
% 2.19/1.45  Simplification rules
% 2.19/1.45  ----------------------
% 2.19/1.45  #Subsume      : 1
% 2.19/1.45  #Demod        : 27
% 2.19/1.45  #Tautology    : 46
% 2.19/1.45  #SimpNegUnit  : 3
% 2.19/1.45  #BackRed      : 0
% 2.19/1.45  
% 2.19/1.45  #Partial instantiations: 0
% 2.19/1.45  #Strategies tried      : 1
% 2.19/1.45  
% 2.19/1.45  Timing (in seconds)
% 2.19/1.45  ----------------------
% 2.19/1.45  Preprocessing        : 0.37
% 2.19/1.45  Parsing              : 0.19
% 2.19/1.45  CNF conversion       : 0.02
% 2.19/1.45  Main loop            : 0.25
% 2.19/1.45  Inferencing          : 0.10
% 2.19/1.45  Reduction            : 0.07
% 2.19/1.45  Demodulation         : 0.04
% 2.19/1.45  BG Simplification    : 0.01
% 2.19/1.45  Subsumption          : 0.04
% 2.19/1.45  Abstraction          : 0.01
% 2.19/1.45  MUC search           : 0.00
% 2.19/1.45  Cooper               : 0.00
% 2.19/1.45  Total                : 0.64
% 2.19/1.45  Index Insertion      : 0.00
% 2.19/1.45  Index Deletion       : 0.00
% 2.19/1.45  Index Matching       : 0.00
% 2.19/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
