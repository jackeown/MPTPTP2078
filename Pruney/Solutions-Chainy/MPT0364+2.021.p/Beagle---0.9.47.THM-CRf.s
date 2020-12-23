%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:41 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   44 (  58 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 107 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

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

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_35,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28])).

tff(c_41,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k3_subset_1(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,k4_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [A_31] :
      ( r1_xboole_0(A_31,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_31,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4])).

tff(c_77,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_30])).

tff(c_83,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_77])).

tff(c_84,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_85,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_16,plain,(
    ! [B_15,A_14,C_17] :
      ( r1_tarski(B_15,k3_subset_1(A_14,C_17))
      | ~ r1_xboole_0(B_15,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_210,plain,(
    ! [B_61,C_62,A_63] :
      ( r1_tarski(B_61,C_62)
      | ~ r1_tarski(k3_subset_1(A_63,C_62),k3_subset_1(A_63,B_61))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_243,plain,(
    ! [C_72,C_73,A_74] :
      ( r1_tarski(C_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_74))
      | ~ r1_xboole_0(k3_subset_1(A_74,C_73),C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(k3_subset_1(A_74,C_73),k1_zfmisc_1(A_74)) ) ),
    inference(resolution,[status(thm)],[c_16,c_210])).

tff(c_270,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_88,c_243])).

tff(c_290,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_270])).

tff(c_291,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_290])).

tff(c_295,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8,c_291])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:05:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.28  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.05/1.28  
% 2.05/1.28  %Foreground sorts:
% 2.05/1.28  
% 2.05/1.28  
% 2.05/1.28  %Background operators:
% 2.05/1.28  
% 2.05/1.28  
% 2.05/1.28  %Foreground operators:
% 2.05/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.05/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.28  
% 2.25/1.29  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 2.25/1.29  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.25/1.29  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.25/1.29  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.25/1.29  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.25/1.29  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.25/1.29  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.25/1.29  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.25/1.29  tff(c_8, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.25/1.29  tff(c_22, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.25/1.29  tff(c_30, plain, (~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.25/1.29  tff(c_28, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.25/1.29  tff(c_35, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_28])).
% 2.25/1.29  tff(c_41, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k3_subset_1(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.25/1.29  tff(c_52, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_41])).
% 2.25/1.29  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, k4_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.29  tff(c_74, plain, (![A_31]: (r1_xboole_0(A_31, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_31, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_4])).
% 2.25/1.29  tff(c_77, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_30])).
% 2.25/1.29  tff(c_83, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_77])).
% 2.25/1.29  tff(c_84, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.25/1.29  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.25/1.29  tff(c_85, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_22])).
% 2.25/1.29  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.29  tff(c_88, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_85, c_2])).
% 2.25/1.29  tff(c_16, plain, (![B_15, A_14, C_17]: (r1_tarski(B_15, k3_subset_1(A_14, C_17)) | ~r1_xboole_0(B_15, C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.25/1.29  tff(c_210, plain, (![B_61, C_62, A_63]: (r1_tarski(B_61, C_62) | ~r1_tarski(k3_subset_1(A_63, C_62), k3_subset_1(A_63, B_61)) | ~m1_subset_1(C_62, k1_zfmisc_1(A_63)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.25/1.29  tff(c_243, plain, (![C_72, C_73, A_74]: (r1_tarski(C_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_74)) | ~r1_xboole_0(k3_subset_1(A_74, C_73), C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_74)) | ~m1_subset_1(k3_subset_1(A_74, C_73), k1_zfmisc_1(A_74)))), inference(resolution, [status(thm)], [c_16, c_210])).
% 2.25/1.29  tff(c_270, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_88, c_243])).
% 2.25/1.29  tff(c_290, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_270])).
% 2.25/1.29  tff(c_291, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_84, c_290])).
% 2.25/1.29  tff(c_295, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_291])).
% 2.25/1.29  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_295])).
% 2.25/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.29  
% 2.25/1.29  Inference rules
% 2.25/1.29  ----------------------
% 2.25/1.29  #Ref     : 0
% 2.25/1.29  #Sup     : 72
% 2.25/1.29  #Fact    : 0
% 2.25/1.29  #Define  : 0
% 2.25/1.29  #Split   : 1
% 2.25/1.29  #Chain   : 0
% 2.25/1.29  #Close   : 0
% 2.25/1.29  
% 2.25/1.29  Ordering : KBO
% 2.25/1.29  
% 2.25/1.29  Simplification rules
% 2.25/1.29  ----------------------
% 2.25/1.29  #Subsume      : 11
% 2.25/1.29  #Demod        : 8
% 2.25/1.29  #Tautology    : 25
% 2.25/1.29  #SimpNegUnit  : 3
% 2.25/1.29  #BackRed      : 0
% 2.25/1.29  
% 2.25/1.29  #Partial instantiations: 0
% 2.25/1.29  #Strategies tried      : 1
% 2.25/1.29  
% 2.25/1.29  Timing (in seconds)
% 2.25/1.29  ----------------------
% 2.25/1.29  Preprocessing        : 0.28
% 2.25/1.29  Parsing              : 0.15
% 2.25/1.29  CNF conversion       : 0.02
% 2.25/1.29  Main loop            : 0.25
% 2.25/1.29  Inferencing          : 0.10
% 2.25/1.29  Reduction            : 0.06
% 2.25/1.29  Demodulation         : 0.04
% 2.25/1.29  BG Simplification    : 0.02
% 2.25/1.29  Subsumption          : 0.05
% 2.25/1.29  Abstraction          : 0.01
% 2.25/1.29  MUC search           : 0.00
% 2.25/1.29  Cooper               : 0.00
% 2.25/1.29  Total                : 0.56
% 2.25/1.29  Index Insertion      : 0.00
% 2.25/1.29  Index Deletion       : 0.00
% 2.25/1.29  Index Matching       : 0.00
% 2.25/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
