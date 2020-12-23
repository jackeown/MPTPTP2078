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
% DateTime   : Thu Dec  3 10:08:49 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :   45 (  53 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 (  96 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_73,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_535,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r2_hidden('#skF_1'(A_95,B_96,C_97),B_96)
      | r2_hidden('#skF_2'(A_95,B_96,C_97),C_97)
      | k4_xboole_0(A_95,B_96) = C_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_871,plain,(
    ! [A_117,C_118] :
      ( r2_hidden('#skF_2'(A_117,A_117,C_118),C_118)
      | k4_xboole_0(A_117,A_117) = C_118 ) ),
    inference(resolution,[status(thm)],[c_18,c_535])).

tff(c_34,plain,(
    ! [A_20] : r1_xboole_0(A_20,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_55,plain,(
    ! [A_19,C_35] :
      ( ~ r1_xboole_0(A_19,k1_xboole_0)
      | ~ r2_hidden(C_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_52])).

tff(c_57,plain,(
    ! [C_35] : ~ r2_hidden(C_35,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_55])).

tff(c_898,plain,(
    ! [A_117] : k4_xboole_0(A_117,A_117) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_871,c_57])).

tff(c_542,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_535])).

tff(c_902,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k1_xboole_0 = C_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_542])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_200,plain,(
    ! [D_67,A_68,B_69] :
      ( ~ r2_hidden(D_67,'#skF_5'(A_68,B_69))
      | ~ r2_hidden(D_67,B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5676,plain,(
    ! [A_274,B_275,B_276] :
      ( ~ r2_hidden('#skF_3'('#skF_5'(A_274,B_275),B_276),B_275)
      | ~ r2_hidden(A_274,B_275)
      | r1_xboole_0('#skF_5'(A_274,B_275),B_276) ) ),
    inference(resolution,[status(thm)],[c_24,c_200])).

tff(c_5692,plain,(
    ! [A_277,B_278] :
      ( ~ r2_hidden(A_277,B_278)
      | r1_xboole_0('#skF_5'(A_277,B_278),B_278) ) ),
    inference(resolution,[status(thm)],[c_22,c_5676])).

tff(c_82,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_5'(A_46,B_47),B_47)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_40,plain,(
    ! [B_29] :
      ( ~ r1_xboole_0(B_29,'#skF_6')
      | ~ r2_hidden(B_29,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_107,plain,(
    ! [A_46] :
      ( ~ r1_xboole_0('#skF_5'(A_46,'#skF_6'),'#skF_6')
      | ~ r2_hidden(A_46,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_40])).

tff(c_5705,plain,(
    ! [A_279] : ~ r2_hidden(A_279,'#skF_6') ),
    inference(resolution,[status(thm)],[c_5692,c_107])).

tff(c_5735,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_902,c_5705])).

tff(c_5773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.95  
% 5.00/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.96  %$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 5.00/1.96  
% 5.00/1.96  %Foreground sorts:
% 5.00/1.96  
% 5.00/1.96  
% 5.00/1.96  %Background operators:
% 5.00/1.96  
% 5.00/1.96  
% 5.00/1.96  %Foreground operators:
% 5.00/1.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.00/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.00/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.00/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.00/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.00/1.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.00/1.96  tff('#skF_6', type, '#skF_6': $i).
% 5.00/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.00/1.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.00/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.00/1.96  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.00/1.96  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.00/1.96  
% 5.00/1.97  tff(f_97, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 5.00/1.97  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.00/1.97  tff(f_73, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.00/1.97  tff(f_71, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.00/1.97  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.00/1.97  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.00/1.97  tff(f_86, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 5.00/1.97  tff(c_42, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.00/1.97  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.00/1.97  tff(c_535, plain, (![A_95, B_96, C_97]: (~r2_hidden('#skF_1'(A_95, B_96, C_97), B_96) | r2_hidden('#skF_2'(A_95, B_96, C_97), C_97) | k4_xboole_0(A_95, B_96)=C_97)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.00/1.97  tff(c_871, plain, (![A_117, C_118]: (r2_hidden('#skF_2'(A_117, A_117, C_118), C_118) | k4_xboole_0(A_117, A_117)=C_118)), inference(resolution, [status(thm)], [c_18, c_535])).
% 5.00/1.97  tff(c_34, plain, (![A_20]: (r1_xboole_0(A_20, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.00/1.97  tff(c_32, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.00/1.97  tff(c_52, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.00/1.97  tff(c_55, plain, (![A_19, C_35]: (~r1_xboole_0(A_19, k1_xboole_0) | ~r2_hidden(C_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_52])).
% 5.00/1.97  tff(c_57, plain, (![C_35]: (~r2_hidden(C_35, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_55])).
% 5.00/1.97  tff(c_898, plain, (![A_117]: (k4_xboole_0(A_117, A_117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_871, c_57])).
% 5.00/1.97  tff(c_542, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_535])).
% 5.00/1.97  tff(c_902, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k1_xboole_0=C_3)), inference(demodulation, [status(thm), theory('equality')], [c_898, c_542])).
% 5.00/1.97  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.00/1.97  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.00/1.97  tff(c_200, plain, (![D_67, A_68, B_69]: (~r2_hidden(D_67, '#skF_5'(A_68, B_69)) | ~r2_hidden(D_67, B_69) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.00/1.97  tff(c_5676, plain, (![A_274, B_275, B_276]: (~r2_hidden('#skF_3'('#skF_5'(A_274, B_275), B_276), B_275) | ~r2_hidden(A_274, B_275) | r1_xboole_0('#skF_5'(A_274, B_275), B_276))), inference(resolution, [status(thm)], [c_24, c_200])).
% 5.00/1.97  tff(c_5692, plain, (![A_277, B_278]: (~r2_hidden(A_277, B_278) | r1_xboole_0('#skF_5'(A_277, B_278), B_278))), inference(resolution, [status(thm)], [c_22, c_5676])).
% 5.00/1.97  tff(c_82, plain, (![A_46, B_47]: (r2_hidden('#skF_5'(A_46, B_47), B_47) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.00/1.97  tff(c_40, plain, (![B_29]: (~r1_xboole_0(B_29, '#skF_6') | ~r2_hidden(B_29, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.00/1.97  tff(c_107, plain, (![A_46]: (~r1_xboole_0('#skF_5'(A_46, '#skF_6'), '#skF_6') | ~r2_hidden(A_46, '#skF_6'))), inference(resolution, [status(thm)], [c_82, c_40])).
% 5.00/1.97  tff(c_5705, plain, (![A_279]: (~r2_hidden(A_279, '#skF_6'))), inference(resolution, [status(thm)], [c_5692, c_107])).
% 5.00/1.97  tff(c_5735, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_902, c_5705])).
% 5.00/1.97  tff(c_5773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_5735])).
% 5.00/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/1.97  
% 5.00/1.97  Inference rules
% 5.00/1.97  ----------------------
% 5.00/1.97  #Ref     : 0
% 5.00/1.97  #Sup     : 1373
% 5.00/1.97  #Fact    : 0
% 5.00/1.97  #Define  : 0
% 5.00/1.97  #Split   : 2
% 5.00/1.97  #Chain   : 0
% 5.00/1.97  #Close   : 0
% 5.00/1.97  
% 5.00/1.97  Ordering : KBO
% 5.00/1.97  
% 5.00/1.97  Simplification rules
% 5.00/1.97  ----------------------
% 5.00/1.97  #Subsume      : 267
% 5.00/1.97  #Demod        : 995
% 5.00/1.97  #Tautology    : 673
% 5.00/1.97  #SimpNegUnit  : 36
% 5.00/1.97  #BackRed      : 2
% 5.00/1.97  
% 5.00/1.97  #Partial instantiations: 0
% 5.00/1.97  #Strategies tried      : 1
% 5.00/1.97  
% 5.00/1.97  Timing (in seconds)
% 5.00/1.97  ----------------------
% 5.00/1.97  Preprocessing        : 0.30
% 5.00/1.97  Parsing              : 0.16
% 5.00/1.97  CNF conversion       : 0.02
% 5.00/1.97  Main loop            : 0.91
% 5.00/1.97  Inferencing          : 0.32
% 5.00/1.97  Reduction            : 0.31
% 5.00/1.97  Demodulation         : 0.23
% 5.00/1.97  BG Simplification    : 0.03
% 5.00/1.97  Subsumption          : 0.19
% 5.00/1.97  Abstraction          : 0.04
% 5.00/1.97  MUC search           : 0.00
% 5.00/1.97  Cooper               : 0.00
% 5.00/1.97  Total                : 1.24
% 5.00/1.97  Index Insertion      : 0.00
% 5.00/1.97  Index Deletion       : 0.00
% 5.00/1.97  Index Matching       : 0.00
% 5.00/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
