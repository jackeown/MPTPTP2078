%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:47 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   39 (  59 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 153 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_14,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [B_9,A_8,C_11] :
      ( r1_tarski(B_9,k3_subset_1(A_8,C_11))
      | ~ r1_xboole_0(B_9,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    ! [C_28,A_29,B_30] :
      ( r1_tarski(C_28,k3_subset_1(A_29,B_30))
      | ~ r1_tarski(B_30,k3_subset_1(A_29,C_28))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [C_31,A_32,B_33] :
      ( r1_tarski(C_31,k3_subset_1(A_32,B_33))
      | ~ r1_xboole_0(B_33,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_8,c_49])).

tff(c_6,plain,(
    ! [B_9,C_11,A_8] :
      ( r1_xboole_0(B_9,C_11)
      | ~ r1_tarski(B_9,k3_subset_1(A_8,C_11))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_70,plain,(
    ! [C_34,B_35,A_36] :
      ( r1_xboole_0(C_34,B_35)
      | ~ r1_xboole_0(B_35,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36)) ) ),
    inference(resolution,[status(thm)],[c_53,c_6])).

tff(c_76,plain,(
    ! [A_36] :
      ( r1_xboole_0('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_36))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_36)) ) ),
    inference(resolution,[status(thm)],[c_12,c_70])).

tff(c_78,plain,(
    ! [A_37] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_37))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_37)) ) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_81,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_78])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_81])).

tff(c_86,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [A_38] :
      ( r1_xboole_0(A_38,'#skF_4')
      | ~ r1_tarski(A_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_35,plain,(
    ! [B_25,A_26,C_27] :
      ( r1_tarski(B_25,k3_subset_1(A_26,C_27))
      | ~ r1_xboole_0(B_25,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_43,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_35,c_10])).

tff(c_48,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_43])).

tff(c_99,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_48])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.21  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.85/1.21  
% 1.85/1.21  %Foreground sorts:
% 1.85/1.21  
% 1.85/1.21  
% 1.85/1.21  %Background operators:
% 1.85/1.21  
% 1.85/1.21  
% 1.85/1.21  %Foreground operators:
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.85/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.85/1.21  
% 1.92/1.22  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_subset_1)).
% 1.92/1.22  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 1.92/1.22  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 1.92/1.22  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.92/1.22  tff(c_14, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.22  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.22  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.22  tff(c_12, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.22  tff(c_8, plain, (![B_9, A_8, C_11]: (r1_tarski(B_9, k3_subset_1(A_8, C_11)) | ~r1_xboole_0(B_9, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.22  tff(c_49, plain, (![C_28, A_29, B_30]: (r1_tarski(C_28, k3_subset_1(A_29, B_30)) | ~r1_tarski(B_30, k3_subset_1(A_29, C_28)) | ~m1_subset_1(C_28, k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.92/1.22  tff(c_53, plain, (![C_31, A_32, B_33]: (r1_tarski(C_31, k3_subset_1(A_32, B_33)) | ~r1_xboole_0(B_33, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(resolution, [status(thm)], [c_8, c_49])).
% 1.92/1.22  tff(c_6, plain, (![B_9, C_11, A_8]: (r1_xboole_0(B_9, C_11) | ~r1_tarski(B_9, k3_subset_1(A_8, C_11)) | ~m1_subset_1(C_11, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.22  tff(c_70, plain, (![C_34, B_35, A_36]: (r1_xboole_0(C_34, B_35) | ~r1_xboole_0(B_35, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_36)) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)))), inference(resolution, [status(thm)], [c_53, c_6])).
% 1.92/1.22  tff(c_76, plain, (![A_36]: (r1_xboole_0('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_36)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_36)))), inference(resolution, [status(thm)], [c_12, c_70])).
% 1.92/1.22  tff(c_78, plain, (![A_37]: (~m1_subset_1('#skF_3', k1_zfmisc_1(A_37)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_37)))), inference(splitLeft, [status(thm)], [c_76])).
% 1.92/1.22  tff(c_81, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_78])).
% 1.92/1.22  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_81])).
% 1.92/1.22  tff(c_86, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_76])).
% 1.92/1.22  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.22  tff(c_94, plain, (![A_38]: (r1_xboole_0(A_38, '#skF_4') | ~r1_tarski(A_38, '#skF_3'))), inference(resolution, [status(thm)], [c_86, c_2])).
% 1.92/1.22  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.22  tff(c_35, plain, (![B_25, A_26, C_27]: (r1_tarski(B_25, k3_subset_1(A_26, C_27)) | ~r1_xboole_0(B_25, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(A_26)) | ~m1_subset_1(B_25, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.22  tff(c_10, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.22  tff(c_43, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_35, c_10])).
% 1.92/1.22  tff(c_48, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_43])).
% 1.92/1.22  tff(c_99, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_94, c_48])).
% 1.92/1.22  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_99])).
% 1.92/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  Inference rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Ref     : 0
% 1.92/1.22  #Sup     : 19
% 1.92/1.22  #Fact    : 0
% 1.92/1.22  #Define  : 0
% 1.92/1.22  #Split   : 2
% 1.92/1.22  #Chain   : 0
% 1.92/1.22  #Close   : 0
% 1.92/1.22  
% 1.92/1.22  Ordering : KBO
% 1.92/1.22  
% 1.92/1.22  Simplification rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Subsume      : 1
% 1.92/1.22  #Demod        : 7
% 1.92/1.22  #Tautology    : 2
% 1.92/1.22  #SimpNegUnit  : 0
% 1.92/1.22  #BackRed      : 0
% 1.92/1.22  
% 1.92/1.22  #Partial instantiations: 0
% 1.92/1.22  #Strategies tried      : 1
% 1.92/1.22  
% 1.92/1.22  Timing (in seconds)
% 1.92/1.22  ----------------------
% 1.92/1.22  Preprocessing        : 0.28
% 1.92/1.22  Parsing              : 0.16
% 1.92/1.22  CNF conversion       : 0.02
% 1.92/1.22  Main loop            : 0.15
% 1.92/1.22  Inferencing          : 0.06
% 1.92/1.22  Reduction            : 0.04
% 1.92/1.22  Demodulation         : 0.03
% 1.97/1.22  BG Simplification    : 0.01
% 1.97/1.22  Subsumption          : 0.03
% 1.97/1.22  Abstraction          : 0.01
% 1.97/1.22  MUC search           : 0.00
% 1.97/1.22  Cooper               : 0.00
% 1.97/1.22  Total                : 0.45
% 1.97/1.22  Index Insertion      : 0.00
% 1.97/1.22  Index Deletion       : 0.00
% 1.97/1.23  Index Matching       : 0.00
% 1.97/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
