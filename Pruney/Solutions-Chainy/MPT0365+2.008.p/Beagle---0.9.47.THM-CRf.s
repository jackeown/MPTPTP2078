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
% DateTime   : Thu Dec  3 09:56:43 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   44 (  71 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 173 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_24,plain,(
    k3_subset_1('#skF_2','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    r1_xboole_0(k3_subset_1('#skF_2','#skF_3'),k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,B_27)
      | ~ r2_hidden(C_28,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [C_37] :
      ( ~ r2_hidden(C_37,k3_subset_1('#skF_2','#skF_4'))
      | ~ r2_hidden(C_37,k3_subset_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_101,plain,(
    ! [A_39] :
      ( ~ r2_hidden('#skF_1'(A_39,k3_subset_1('#skF_2','#skF_3')),k3_subset_1('#skF_2','#skF_4'))
      | r1_xboole_0(A_39,k3_subset_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_106,plain,(
    r1_xboole_0(k3_subset_1('#skF_2','#skF_4'),k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_143,plain,(
    ! [B_53,C_54,A_55] :
      ( r1_tarski(B_53,C_54)
      | ~ r1_xboole_0(B_53,k3_subset_1(A_55,C_54))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_150,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_106,c_143])).

tff(c_160,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_150])).

tff(c_381,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_400,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_381])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_400])).

tff(c_405,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_135,plain,(
    ! [B_50,A_51,C_52] :
      ( r1_tarski(B_50,k3_subset_1(A_51,C_52))
      | ~ r1_xboole_0(B_50,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_142,plain,(
    ! [A_51,C_52,B_50] :
      ( k3_subset_1(A_51,C_52) = B_50
      | ~ r1_tarski(k3_subset_1(A_51,C_52),B_50)
      | ~ r1_xboole_0(B_50,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_135,c_8])).

tff(c_409,plain,
    ( k3_subset_1('#skF_2','#skF_4') = '#skF_3'
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_405,c_142])).

tff(c_414,plain,(
    k3_subset_1('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_409])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:17:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.14/1.29  
% 2.14/1.29  %Foreground sorts:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Background operators:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Foreground operators:
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.14/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.29  
% 2.14/1.31  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_subset_1)).
% 2.14/1.31  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.14/1.31  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.14/1.31  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 2.14/1.31  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.14/1.31  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.31  tff(c_24, plain, (k3_subset_1('#skF_2', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.31  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.31  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.31  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.31  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.31  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.31  tff(c_26, plain, (r1_xboole_0(k3_subset_1('#skF_2', '#skF_3'), k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.31  tff(c_44, plain, (![A_26, B_27, C_28]: (~r1_xboole_0(A_26, B_27) | ~r2_hidden(C_28, B_27) | ~r2_hidden(C_28, A_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.31  tff(c_83, plain, (![C_37]: (~r2_hidden(C_37, k3_subset_1('#skF_2', '#skF_4')) | ~r2_hidden(C_37, k3_subset_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_26, c_44])).
% 2.14/1.31  tff(c_101, plain, (![A_39]: (~r2_hidden('#skF_1'(A_39, k3_subset_1('#skF_2', '#skF_3')), k3_subset_1('#skF_2', '#skF_4')) | r1_xboole_0(A_39, k3_subset_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_4, c_83])).
% 2.14/1.31  tff(c_106, plain, (r1_xboole_0(k3_subset_1('#skF_2', '#skF_4'), k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_101])).
% 2.14/1.31  tff(c_143, plain, (![B_53, C_54, A_55]: (r1_tarski(B_53, C_54) | ~r1_xboole_0(B_53, k3_subset_1(A_55, C_54)) | ~m1_subset_1(C_54, k1_zfmisc_1(A_55)) | ~m1_subset_1(B_53, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.14/1.31  tff(c_150, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_4'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_106, c_143])).
% 2.14/1.31  tff(c_160, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_4'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_150])).
% 2.14/1.31  tff(c_381, plain, (~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_160])).
% 2.14/1.31  tff(c_400, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_381])).
% 2.14/1.31  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_400])).
% 2.14/1.31  tff(c_405, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_160])).
% 2.14/1.31  tff(c_135, plain, (![B_50, A_51, C_52]: (r1_tarski(B_50, k3_subset_1(A_51, C_52)) | ~r1_xboole_0(B_50, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_51)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.31  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.31  tff(c_142, plain, (![A_51, C_52, B_50]: (k3_subset_1(A_51, C_52)=B_50 | ~r1_tarski(k3_subset_1(A_51, C_52), B_50) | ~r1_xboole_0(B_50, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_51)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_135, c_8])).
% 2.14/1.31  tff(c_409, plain, (k3_subset_1('#skF_2', '#skF_4')='#skF_3' | ~r1_xboole_0('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_405, c_142])).
% 2.14/1.31  tff(c_414, plain, (k3_subset_1('#skF_2', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_409])).
% 2.14/1.31  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_414])).
% 2.14/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.31  
% 2.14/1.31  Inference rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Ref     : 0
% 2.14/1.31  #Sup     : 69
% 2.14/1.31  #Fact    : 0
% 2.14/1.31  #Define  : 0
% 2.14/1.31  #Split   : 5
% 2.14/1.31  #Chain   : 0
% 2.14/1.31  #Close   : 0
% 2.14/1.31  
% 2.14/1.31  Ordering : KBO
% 2.14/1.31  
% 2.14/1.31  Simplification rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Subsume      : 7
% 2.14/1.31  #Demod        : 54
% 2.14/1.31  #Tautology    : 22
% 2.14/1.31  #SimpNegUnit  : 3
% 2.14/1.31  #BackRed      : 7
% 2.14/1.31  
% 2.14/1.31  #Partial instantiations: 0
% 2.14/1.31  #Strategies tried      : 1
% 2.14/1.31  
% 2.14/1.31  Timing (in seconds)
% 2.14/1.31  ----------------------
% 2.14/1.31  Preprocessing        : 0.28
% 2.14/1.31  Parsing              : 0.16
% 2.14/1.31  CNF conversion       : 0.02
% 2.14/1.31  Main loop            : 0.28
% 2.14/1.31  Inferencing          : 0.11
% 2.14/1.31  Reduction            : 0.07
% 2.14/1.31  Demodulation         : 0.05
% 2.14/1.31  BG Simplification    : 0.02
% 2.14/1.31  Subsumption          : 0.06
% 2.14/1.31  Abstraction          : 0.01
% 2.14/1.31  MUC search           : 0.00
% 2.14/1.31  Cooper               : 0.00
% 2.14/1.31  Total                : 0.58
% 2.14/1.31  Index Insertion      : 0.00
% 2.14/1.31  Index Deletion       : 0.00
% 2.14/1.31  Index Matching       : 0.00
% 2.14/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
