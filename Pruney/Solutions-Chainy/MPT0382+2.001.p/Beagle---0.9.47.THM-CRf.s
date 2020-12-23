%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:06 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 136 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 314 expanded)
%              Number of equality atoms :   24 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( k3_subset_1(A,B) = k3_subset_1(A,C)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_43,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_43])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_115,plain,(
    ! [B_45,A_46,C_47] :
      ( r1_xboole_0(B_45,k3_subset_1(A_46,C_47))
      | ~ r1_tarski(B_45,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    k3_subset_1('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_102,plain,(
    ! [B_39,C_40,A_41] :
      ( r1_tarski(B_39,C_40)
      | ~ r1_xboole_0(B_39,k3_subset_1(A_41,C_40))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_105,plain,(
    ! [B_39] :
      ( r1_tarski(B_39,'#skF_2')
      | ~ r1_xboole_0(B_39,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_39,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_102])).

tff(c_107,plain,(
    ! [B_39] :
      ( r1_tarski(B_39,'#skF_2')
      | ~ r1_xboole_0(B_39,k3_subset_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_39,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_105])).

tff(c_119,plain,(
    ! [B_45] :
      ( r1_tarski(B_45,'#skF_2')
      | ~ r1_tarski(B_45,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_45,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_115,c_107])).

tff(c_143,plain,(
    ! [B_49] :
      ( r1_tarski(B_49,'#skF_2')
      | ~ r1_tarski(B_49,'#skF_3')
      | ~ m1_subset_1(B_49,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_119])).

tff(c_150,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_143])).

tff(c_152,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_155,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_155])).

tff(c_160,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_160,c_14])).

tff(c_151,plain,
    ( r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_143])).

tff(c_212,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_125,plain,(
    ! [B_45] :
      ( r1_xboole_0(B_45,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_45,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_45,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_115])).

tff(c_132,plain,(
    ! [B_48] :
      ( r1_xboole_0(B_48,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(B_48,'#skF_2')
      | ~ m1_subset_1(B_48,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_125])).

tff(c_24,plain,(
    ! [B_16,C_18,A_15] :
      ( r1_tarski(B_16,C_18)
      | ~ r1_xboole_0(B_16,k3_subset_1(A_15,C_18))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    ! [B_48] :
      ( r1_tarski(B_48,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(B_48,'#skF_2')
      | ~ m1_subset_1(B_48,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_132,c_24])).

tff(c_217,plain,(
    ! [B_53] :
      ( r1_tarski(B_53,'#skF_3')
      | ~ r1_tarski(B_53,'#skF_2')
      | ~ m1_subset_1(B_53,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_138])).

tff(c_223,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_217])).

tff(c_229,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_223])).

tff(c_232,plain,(
    k4_xboole_0('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_229])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_232])).

tff(c_238,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_72,plain,(
    ! [A_33,B_34] :
      ( r2_xboole_0(A_33,B_34)
      | B_34 = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k4_xboole_0(B_6,A_5) != k1_xboole_0
      | ~ r2_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_83,plain,(
    ! [B_34,A_33] :
      ( k4_xboole_0(B_34,A_33) != k1_xboole_0
      | B_34 = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_72,c_10])).

tff(c_253,plain,
    ( k4_xboole_0('#skF_3','#skF_2') != k1_xboole_0
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_238,c_83])).

tff(c_259,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_253])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:06:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.28  
% 2.02/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  %$ r2_xboole_0 > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.29  
% 2.02/1.29  %Foreground sorts:
% 2.02/1.29  
% 2.02/1.29  
% 2.02/1.29  %Background operators:
% 2.02/1.29  
% 2.02/1.29  
% 2.02/1.29  %Foreground operators:
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.02/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.29  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.29  
% 2.02/1.30  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((k3_subset_1(A, B) = k3_subset_1(A, C)) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_subset_1)).
% 2.02/1.30  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.02/1.30  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.02/1.30  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.02/1.30  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 2.02/1.30  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.02/1.30  tff(f_39, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 2.02/1.30  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.02/1.30  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.30  tff(c_43, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.30  tff(c_50, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_43])).
% 2.02/1.30  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.30  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.02/1.30  tff(c_115, plain, (![B_45, A_46, C_47]: (r1_xboole_0(B_45, k3_subset_1(A_46, C_47)) | ~r1_tarski(B_45, C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(A_46)) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.30  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.02/1.30  tff(c_28, plain, (k3_subset_1('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.02/1.30  tff(c_102, plain, (![B_39, C_40, A_41]: (r1_tarski(B_39, C_40) | ~r1_xboole_0(B_39, k3_subset_1(A_41, C_40)) | ~m1_subset_1(C_40, k1_zfmisc_1(A_41)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.30  tff(c_105, plain, (![B_39]: (r1_tarski(B_39, '#skF_2') | ~r1_xboole_0(B_39, k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_39, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_102])).
% 2.02/1.30  tff(c_107, plain, (![B_39]: (r1_tarski(B_39, '#skF_2') | ~r1_xboole_0(B_39, k3_subset_1('#skF_1', '#skF_3')) | ~m1_subset_1(B_39, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_105])).
% 2.02/1.30  tff(c_119, plain, (![B_45]: (r1_tarski(B_45, '#skF_2') | ~r1_tarski(B_45, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_45, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_115, c_107])).
% 2.02/1.30  tff(c_143, plain, (![B_49]: (r1_tarski(B_49, '#skF_2') | ~r1_tarski(B_49, '#skF_3') | ~m1_subset_1(B_49, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_119])).
% 2.02/1.30  tff(c_150, plain, (r1_tarski('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_143])).
% 2.02/1.30  tff(c_152, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_150])).
% 2.02/1.30  tff(c_155, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_152])).
% 2.02/1.30  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_155])).
% 2.02/1.30  tff(c_160, plain, (r1_tarski('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_150])).
% 2.02/1.30  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.30  tff(c_171, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_160, c_14])).
% 2.02/1.30  tff(c_151, plain, (r1_tarski('#skF_2', '#skF_2') | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_143])).
% 2.02/1.30  tff(c_212, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_151])).
% 2.02/1.30  tff(c_125, plain, (![B_45]: (r1_xboole_0(B_45, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(B_45, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_45, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_115])).
% 2.02/1.30  tff(c_132, plain, (![B_48]: (r1_xboole_0(B_48, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(B_48, '#skF_2') | ~m1_subset_1(B_48, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_125])).
% 2.02/1.30  tff(c_24, plain, (![B_16, C_18, A_15]: (r1_tarski(B_16, C_18) | ~r1_xboole_0(B_16, k3_subset_1(A_15, C_18)) | ~m1_subset_1(C_18, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.30  tff(c_138, plain, (![B_48]: (r1_tarski(B_48, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~r1_tarski(B_48, '#skF_2') | ~m1_subset_1(B_48, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_132, c_24])).
% 2.02/1.30  tff(c_217, plain, (![B_53]: (r1_tarski(B_53, '#skF_3') | ~r1_tarski(B_53, '#skF_2') | ~m1_subset_1(B_53, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_138])).
% 2.02/1.30  tff(c_223, plain, (r1_tarski('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_217])).
% 2.02/1.30  tff(c_229, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_212, c_223])).
% 2.02/1.30  tff(c_232, plain, (k4_xboole_0('#skF_2', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_229])).
% 2.02/1.30  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_232])).
% 2.02/1.30  tff(c_238, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_151])).
% 2.02/1.30  tff(c_72, plain, (![A_33, B_34]: (r2_xboole_0(A_33, B_34) | B_34=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.30  tff(c_10, plain, (![B_6, A_5]: (k4_xboole_0(B_6, A_5)!=k1_xboole_0 | ~r2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.30  tff(c_83, plain, (![B_34, A_33]: (k4_xboole_0(B_34, A_33)!=k1_xboole_0 | B_34=A_33 | ~r1_tarski(A_33, B_34))), inference(resolution, [status(thm)], [c_72, c_10])).
% 2.02/1.30  tff(c_253, plain, (k4_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0 | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_238, c_83])).
% 2.02/1.30  tff(c_259, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_253])).
% 2.02/1.30  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_259])).
% 2.02/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.30  
% 2.02/1.30  Inference rules
% 2.02/1.30  ----------------------
% 2.02/1.30  #Ref     : 0
% 2.02/1.30  #Sup     : 45
% 2.02/1.30  #Fact    : 0
% 2.02/1.30  #Define  : 0
% 2.02/1.30  #Split   : 2
% 2.02/1.30  #Chain   : 0
% 2.02/1.30  #Close   : 0
% 2.02/1.30  
% 2.02/1.30  Ordering : KBO
% 2.02/1.30  
% 2.02/1.30  Simplification rules
% 2.02/1.30  ----------------------
% 2.02/1.30  #Subsume      : 2
% 2.02/1.30  #Demod        : 18
% 2.02/1.30  #Tautology    : 22
% 2.02/1.30  #SimpNegUnit  : 4
% 2.02/1.30  #BackRed      : 0
% 2.02/1.30  
% 2.02/1.30  #Partial instantiations: 0
% 2.02/1.30  #Strategies tried      : 1
% 2.02/1.30  
% 2.02/1.30  Timing (in seconds)
% 2.02/1.30  ----------------------
% 2.02/1.30  Preprocessing        : 0.31
% 2.02/1.30  Parsing              : 0.17
% 2.02/1.30  CNF conversion       : 0.02
% 2.02/1.30  Main loop            : 0.19
% 2.02/1.30  Inferencing          : 0.07
% 2.02/1.30  Reduction            : 0.05
% 2.02/1.30  Demodulation         : 0.04
% 2.02/1.30  BG Simplification    : 0.01
% 2.28/1.30  Subsumption          : 0.04
% 2.28/1.30  Abstraction          : 0.01
% 2.28/1.30  MUC search           : 0.00
% 2.28/1.30  Cooper               : 0.00
% 2.28/1.30  Total                : 0.53
% 2.28/1.30  Index Insertion      : 0.00
% 2.28/1.30  Index Deletion       : 0.00
% 2.28/1.30  Index Matching       : 0.00
% 2.28/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
