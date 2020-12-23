%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:48 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   44 (  66 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 127 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,B)
               => r2_hidden(D,C) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_subset_1)).

tff(c_28,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_78,plain,(
    ! [B_35,A_36] :
      ( r2_hidden(B_35,A_36)
      | ~ m1_subset_1(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [B_35,A_3] :
      ( r1_tarski(B_35,A_3)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_78,c_8])).

tff(c_86,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(B_37,A_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_82])).

tff(c_98,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_86])).

tff(c_101,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_101])).

tff(c_108,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_103])).

tff(c_36,plain,(
    ! [A_13,B_14,C_18] :
      ( m1_subset_1('#skF_3'(A_13,B_14,C_18),B_14)
      | r1_tarski(B_14,C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    ! [C_21] :
      ( r2_hidden(C_21,'#skF_5')
      | ~ m1_subset_1(C_21,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_221,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r2_hidden('#skF_3'(A_63,B_64,C_65),C_65)
      | r1_tarski(B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_274,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(B_74,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_75))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ m1_subset_1('#skF_3'(A_75,B_74,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_221])).

tff(c_278,plain,(
    ! [A_13] :
      ( r1_tarski('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_13))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_36,c_274])).

tff(c_286,plain,(
    ! [A_76] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_76))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_76)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_108,c_278])).

tff(c_296,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_286])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:42:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.29  
% 2.36/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.36/1.29  
% 2.36/1.29  %Foreground sorts:
% 2.36/1.29  
% 2.36/1.29  
% 2.36/1.29  %Background operators:
% 2.36/1.29  
% 2.36/1.29  
% 2.36/1.29  %Foreground operators:
% 2.36/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.36/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.36/1.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.36/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.29  
% 2.36/1.30  tff(f_53, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.36/1.30  tff(f_55, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.36/1.30  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 2.36/1.30  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.36/1.30  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.36/1.30  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.36/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.36/1.30  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, B) => r2_hidden(D, C))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_subset_1)).
% 2.36/1.30  tff(c_28, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.30  tff(c_30, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.30  tff(c_43, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 2.36/1.30  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.36/1.30  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.36/1.30  tff(c_32, plain, (![A_12]: (~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.30  tff(c_78, plain, (![B_35, A_36]: (r2_hidden(B_35, A_36) | ~m1_subset_1(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.36/1.30  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.36/1.30  tff(c_82, plain, (![B_35, A_3]: (r1_tarski(B_35, A_3) | ~m1_subset_1(B_35, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_78, c_8])).
% 2.36/1.30  tff(c_86, plain, (![B_37, A_38]: (r1_tarski(B_37, A_38) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)))), inference(negUnitSimplification, [status(thm)], [c_32, c_82])).
% 2.36/1.30  tff(c_98, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_86])).
% 2.36/1.30  tff(c_101, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.30  tff(c_103, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_98, c_101])).
% 2.36/1.30  tff(c_108, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_103])).
% 2.36/1.30  tff(c_36, plain, (![A_13, B_14, C_18]: (m1_subset_1('#skF_3'(A_13, B_14, C_18), B_14) | r1_tarski(B_14, C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.36/1.30  tff(c_40, plain, (![C_21]: (r2_hidden(C_21, '#skF_5') | ~m1_subset_1(C_21, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.36/1.30  tff(c_221, plain, (![A_63, B_64, C_65]: (~r2_hidden('#skF_3'(A_63, B_64, C_65), C_65) | r1_tarski(B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.36/1.30  tff(c_274, plain, (![B_74, A_75]: (r1_tarski(B_74, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_75)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~m1_subset_1('#skF_3'(A_75, B_74, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_221])).
% 2.36/1.30  tff(c_278, plain, (![A_13]: (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_13)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_36, c_274])).
% 2.36/1.30  tff(c_286, plain, (![A_76]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_76)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_76)))), inference(negUnitSimplification, [status(thm)], [c_108, c_108, c_278])).
% 2.36/1.30  tff(c_296, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_286])).
% 2.36/1.30  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_296])).
% 2.36/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.30  
% 2.36/1.30  Inference rules
% 2.36/1.30  ----------------------
% 2.36/1.30  #Ref     : 0
% 2.36/1.30  #Sup     : 49
% 2.36/1.30  #Fact    : 0
% 2.36/1.30  #Define  : 0
% 2.36/1.30  #Split   : 1
% 2.36/1.30  #Chain   : 0
% 2.36/1.30  #Close   : 0
% 2.36/1.30  
% 2.36/1.30  Ordering : KBO
% 2.36/1.30  
% 2.36/1.30  Simplification rules
% 2.36/1.30  ----------------------
% 2.36/1.30  #Subsume      : 7
% 2.36/1.30  #Demod        : 7
% 2.36/1.30  #Tautology    : 14
% 2.36/1.30  #SimpNegUnit  : 8
% 2.36/1.30  #BackRed      : 0
% 2.36/1.30  
% 2.36/1.30  #Partial instantiations: 0
% 2.36/1.30  #Strategies tried      : 1
% 2.36/1.30  
% 2.36/1.30  Timing (in seconds)
% 2.36/1.30  ----------------------
% 2.36/1.31  Preprocessing        : 0.31
% 2.36/1.31  Parsing              : 0.16
% 2.36/1.31  CNF conversion       : 0.02
% 2.36/1.31  Main loop            : 0.26
% 2.36/1.31  Inferencing          : 0.10
% 2.36/1.31  Reduction            : 0.07
% 2.36/1.31  Demodulation         : 0.05
% 2.36/1.31  BG Simplification    : 0.02
% 2.36/1.31  Subsumption          : 0.07
% 2.36/1.31  Abstraction          : 0.01
% 2.36/1.31  MUC search           : 0.00
% 2.36/1.31  Cooper               : 0.00
% 2.36/1.31  Total                : 0.61
% 2.36/1.31  Index Insertion      : 0.00
% 2.36/1.31  Index Deletion       : 0.00
% 2.36/1.31  Index Matching       : 0.00
% 2.36/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
