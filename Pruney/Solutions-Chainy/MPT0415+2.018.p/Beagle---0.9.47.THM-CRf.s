%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:47 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   41 (  58 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  81 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_63,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_72,plain,(
    ! [A_1,A_40] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_40,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_73,plain,(
    ! [A_40] : ~ r2_hidden(A_40,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_1123,plain,(
    ! [A_151,B_152,C_153] :
      ( r2_hidden('#skF_2'(A_151,B_152,C_153),C_153)
      | r2_hidden(k3_subset_1(A_151,'#skF_2'(A_151,B_152,C_153)),B_152)
      | k7_setfam_1(A_151,B_152) = C_153
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k1_zfmisc_1(A_151)))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k1_zfmisc_1(A_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1159,plain,(
    ! [A_151,C_153] :
      ( r2_hidden('#skF_2'(A_151,k1_xboole_0,C_153),C_153)
      | k7_setfam_1(A_151,k1_xboole_0) = C_153
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k1_zfmisc_1(A_151)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_151))) ) ),
    inference(resolution,[status(thm)],[c_1123,c_73])).

tff(c_1222,plain,(
    ! [A_158,C_159] :
      ( r2_hidden('#skF_2'(A_158,k1_xboole_0,C_159),C_159)
      | k7_setfam_1(A_158,k1_xboole_0) = C_159
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k1_zfmisc_1(A_158))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1159])).

tff(c_1238,plain,(
    ! [A_158] :
      ( r2_hidden('#skF_2'(A_158,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k7_setfam_1(A_158,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1222])).

tff(c_1275,plain,(
    ! [A_160] : k7_setfam_1(A_160,k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1238])).

tff(c_38,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_102,plain,(
    ! [A_55,B_56] :
      ( k7_setfam_1(A_55,k7_setfam_1(A_55,B_56)) = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_107,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_113,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_107])).

tff(c_1313,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1275,c_113])).

tff(c_1345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1313])).

tff(c_1346,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1346,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.50  
% 3.29/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.29/1.50  
% 3.29/1.50  %Foreground sorts:
% 3.29/1.50  
% 3.29/1.50  
% 3.29/1.50  %Background operators:
% 3.29/1.50  
% 3.29/1.50  
% 3.29/1.50  %Foreground operators:
% 3.29/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.29/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.50  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.29/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.29/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.29/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.29/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.50  
% 3.29/1.51  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 3.29/1.51  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.29/1.51  tff(f_81, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.29/1.51  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 3.29/1.51  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.29/1.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.29/1.51  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.29/1.51  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.29/1.51  tff(c_63, plain, (![C_38, B_39, A_40]: (~v1_xboole_0(C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.29/1.51  tff(c_72, plain, (![A_1, A_40]: (~v1_xboole_0(A_1) | ~r2_hidden(A_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_63])).
% 3.29/1.51  tff(c_73, plain, (![A_40]: (~r2_hidden(A_40, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_72])).
% 3.29/1.51  tff(c_1123, plain, (![A_151, B_152, C_153]: (r2_hidden('#skF_2'(A_151, B_152, C_153), C_153) | r2_hidden(k3_subset_1(A_151, '#skF_2'(A_151, B_152, C_153)), B_152) | k7_setfam_1(A_151, B_152)=C_153 | ~m1_subset_1(C_153, k1_zfmisc_1(k1_zfmisc_1(A_151))) | ~m1_subset_1(B_152, k1_zfmisc_1(k1_zfmisc_1(A_151))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.51  tff(c_1159, plain, (![A_151, C_153]: (r2_hidden('#skF_2'(A_151, k1_xboole_0, C_153), C_153) | k7_setfam_1(A_151, k1_xboole_0)=C_153 | ~m1_subset_1(C_153, k1_zfmisc_1(k1_zfmisc_1(A_151))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_151))))), inference(resolution, [status(thm)], [c_1123, c_73])).
% 3.29/1.51  tff(c_1222, plain, (![A_158, C_159]: (r2_hidden('#skF_2'(A_158, k1_xboole_0, C_159), C_159) | k7_setfam_1(A_158, k1_xboole_0)=C_159 | ~m1_subset_1(C_159, k1_zfmisc_1(k1_zfmisc_1(A_158))))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1159])).
% 3.29/1.51  tff(c_1238, plain, (![A_158]: (r2_hidden('#skF_2'(A_158, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1(A_158, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1222])).
% 3.29/1.51  tff(c_1275, plain, (![A_160]: (k7_setfam_1(A_160, k1_xboole_0)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_73, c_1238])).
% 3.29/1.51  tff(c_38, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.29/1.51  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.29/1.51  tff(c_102, plain, (![A_55, B_56]: (k7_setfam_1(A_55, k7_setfam_1(A_55, B_56))=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.51  tff(c_107, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_42, c_102])).
% 3.29/1.51  tff(c_113, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_107])).
% 3.29/1.51  tff(c_1313, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1275, c_113])).
% 3.29/1.51  tff(c_1345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1313])).
% 3.29/1.51  tff(c_1346, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_72])).
% 3.29/1.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.29/1.51  tff(c_1348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1346, c_2])).
% 3.29/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.51  
% 3.29/1.51  Inference rules
% 3.29/1.51  ----------------------
% 3.29/1.51  #Ref     : 0
% 3.29/1.51  #Sup     : 301
% 3.29/1.51  #Fact    : 0
% 3.29/1.51  #Define  : 0
% 3.29/1.51  #Split   : 5
% 3.29/1.51  #Chain   : 0
% 3.29/1.51  #Close   : 0
% 3.29/1.51  
% 3.29/1.51  Ordering : KBO
% 3.29/1.51  
% 3.29/1.51  Simplification rules
% 3.29/1.51  ----------------------
% 3.29/1.51  #Subsume      : 67
% 3.29/1.51  #Demod        : 259
% 3.29/1.51  #Tautology    : 128
% 3.29/1.51  #SimpNegUnit  : 7
% 3.29/1.51  #BackRed      : 13
% 3.29/1.51  
% 3.29/1.51  #Partial instantiations: 0
% 3.29/1.51  #Strategies tried      : 1
% 3.29/1.51  
% 3.29/1.51  Timing (in seconds)
% 3.29/1.51  ----------------------
% 3.29/1.51  Preprocessing        : 0.30
% 3.29/1.51  Parsing              : 0.16
% 3.29/1.51  CNF conversion       : 0.02
% 3.29/1.51  Main loop            : 0.46
% 3.29/1.51  Inferencing          : 0.16
% 3.29/1.51  Reduction            : 0.14
% 3.29/1.51  Demodulation         : 0.10
% 3.29/1.51  BG Simplification    : 0.02
% 3.29/1.51  Subsumption          : 0.10
% 3.29/1.51  Abstraction          : 0.02
% 3.29/1.51  MUC search           : 0.00
% 3.29/1.51  Cooper               : 0.00
% 3.29/1.51  Total                : 0.78
% 3.29/1.51  Index Insertion      : 0.00
% 3.29/1.51  Index Deletion       : 0.00
% 3.29/1.51  Index Matching       : 0.00
% 3.29/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
