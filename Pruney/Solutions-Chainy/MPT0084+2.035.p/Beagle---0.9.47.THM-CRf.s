%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:08 EST 2020

% Result     : Theorem 6.31s
% Output     : CNFRefutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 105 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 241 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_52,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_34,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_35,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_39,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_35])).

tff(c_60,plain,(
    ! [D_25,B_26,A_27] :
      ( r2_hidden(D_25,B_26)
      | ~ r2_hidden(D_25,k3_xboole_0(A_27,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_187,plain,(
    ! [A_44,A_45,B_46] :
      ( r2_hidden('#skF_3'(A_44,k3_xboole_0(A_45,B_46)),B_46)
      | r1_xboole_0(A_44,k3_xboole_0(A_45,B_46)) ) ),
    inference(resolution,[status(thm)],[c_22,c_60])).

tff(c_217,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_3'(A_44,'#skF_4'),'#skF_6')
      | r1_xboole_0(A_44,k3_xboole_0('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_187])).

tff(c_225,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_3'(A_44,'#skF_4'),'#skF_6')
      | r1_xboole_0(A_44,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_217])).

tff(c_134,plain,(
    ! [D_37,A_38,B_39] :
      ( r2_hidden(D_37,k3_xboole_0(A_38,B_39))
      | ~ r2_hidden(D_37,B_39)
      | ~ r2_hidden(D_37,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_90,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,B_32)
      | ~ r2_hidden(C_33,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,(
    ! [C_33] :
      ( ~ r2_hidden(C_33,k3_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_33,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_90])).

tff(c_165,plain,(
    ! [D_41] :
      ( ~ r2_hidden(D_41,'#skF_4')
      | ~ r2_hidden(D_41,'#skF_6')
      | ~ r2_hidden(D_41,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_134,c_93])).

tff(c_3686,plain,(
    ! [B_197] :
      ( ~ r2_hidden('#skF_3'('#skF_5',B_197),'#skF_4')
      | ~ r2_hidden('#skF_3'('#skF_5',B_197),'#skF_6')
      | r1_xboole_0('#skF_5',B_197) ) ),
    inference(resolution,[status(thm)],[c_24,c_165])).

tff(c_3712,plain,
    ( ~ r2_hidden('#skF_3'('#skF_5','#skF_4'),'#skF_4')
    | r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_225,c_3686])).

tff(c_3716,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3712])).

tff(c_3720,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_3716])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3749,plain,(
    ! [C_199] :
      ( ~ r2_hidden(C_199,'#skF_4')
      | ~ r2_hidden(C_199,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3720,c_20])).

tff(c_4932,plain,(
    ! [A_218] :
      ( ~ r2_hidden('#skF_3'(A_218,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_218,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_3749])).

tff(c_4948,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_4932])).

tff(c_4955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_4948])).

tff(c_4956,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3712])).

tff(c_4986,plain,(
    ! [C_220] :
      ( ~ r2_hidden(C_220,'#skF_4')
      | ~ r2_hidden(C_220,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4956,c_20])).

tff(c_5479,plain,(
    ! [A_230] :
      ( ~ r2_hidden('#skF_3'(A_230,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_230,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_4986])).

tff(c_5495,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_5479])).

tff(c_5502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_5495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:02:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.31/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.34  
% 6.31/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 6.31/2.34  
% 6.31/2.34  %Foreground sorts:
% 6.31/2.34  
% 6.31/2.34  
% 6.31/2.34  %Background operators:
% 6.31/2.34  
% 6.31/2.34  
% 6.31/2.34  %Foreground operators:
% 6.31/2.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.31/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.31/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.31/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.31/2.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.31/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.31/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.31/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.31/2.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.31/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.31/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.31/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.31/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.31/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.31/2.34  
% 6.31/2.35  tff(f_67, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 6.31/2.35  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.31/2.35  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.31/2.35  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.31/2.35  tff(c_34, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.31/2.35  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.31/2.35  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.31/2.35  tff(c_32, plain, (r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.31/2.35  tff(c_35, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.31/2.35  tff(c_39, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_35])).
% 6.31/2.35  tff(c_60, plain, (![D_25, B_26, A_27]: (r2_hidden(D_25, B_26) | ~r2_hidden(D_25, k3_xboole_0(A_27, B_26)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.31/2.35  tff(c_187, plain, (![A_44, A_45, B_46]: (r2_hidden('#skF_3'(A_44, k3_xboole_0(A_45, B_46)), B_46) | r1_xboole_0(A_44, k3_xboole_0(A_45, B_46)))), inference(resolution, [status(thm)], [c_22, c_60])).
% 6.31/2.35  tff(c_217, plain, (![A_44]: (r2_hidden('#skF_3'(A_44, '#skF_4'), '#skF_6') | r1_xboole_0(A_44, k3_xboole_0('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_39, c_187])).
% 6.31/2.35  tff(c_225, plain, (![A_44]: (r2_hidden('#skF_3'(A_44, '#skF_4'), '#skF_6') | r1_xboole_0(A_44, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_217])).
% 6.31/2.35  tff(c_134, plain, (![D_37, A_38, B_39]: (r2_hidden(D_37, k3_xboole_0(A_38, B_39)) | ~r2_hidden(D_37, B_39) | ~r2_hidden(D_37, A_38))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.31/2.35  tff(c_30, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.31/2.35  tff(c_90, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, B_32) | ~r2_hidden(C_33, A_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.31/2.35  tff(c_93, plain, (![C_33]: (~r2_hidden(C_33, k3_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(C_33, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_90])).
% 6.31/2.35  tff(c_165, plain, (![D_41]: (~r2_hidden(D_41, '#skF_4') | ~r2_hidden(D_41, '#skF_6') | ~r2_hidden(D_41, '#skF_5'))), inference(resolution, [status(thm)], [c_134, c_93])).
% 6.31/2.35  tff(c_3686, plain, (![B_197]: (~r2_hidden('#skF_3'('#skF_5', B_197), '#skF_4') | ~r2_hidden('#skF_3'('#skF_5', B_197), '#skF_6') | r1_xboole_0('#skF_5', B_197))), inference(resolution, [status(thm)], [c_24, c_165])).
% 6.31/2.35  tff(c_3712, plain, (~r2_hidden('#skF_3'('#skF_5', '#skF_4'), '#skF_4') | r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_225, c_3686])).
% 6.31/2.35  tff(c_3716, plain, (~r2_hidden('#skF_3'('#skF_5', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3712])).
% 6.31/2.35  tff(c_3720, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_3716])).
% 6.31/2.35  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.31/2.35  tff(c_3749, plain, (![C_199]: (~r2_hidden(C_199, '#skF_4') | ~r2_hidden(C_199, '#skF_5'))), inference(resolution, [status(thm)], [c_3720, c_20])).
% 6.31/2.35  tff(c_4932, plain, (![A_218]: (~r2_hidden('#skF_3'(A_218, '#skF_5'), '#skF_4') | r1_xboole_0(A_218, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_3749])).
% 6.31/2.35  tff(c_4948, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_4932])).
% 6.31/2.35  tff(c_4955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_4948])).
% 6.31/2.35  tff(c_4956, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_3712])).
% 6.31/2.35  tff(c_4986, plain, (![C_220]: (~r2_hidden(C_220, '#skF_4') | ~r2_hidden(C_220, '#skF_5'))), inference(resolution, [status(thm)], [c_4956, c_20])).
% 6.31/2.35  tff(c_5479, plain, (![A_230]: (~r2_hidden('#skF_3'(A_230, '#skF_5'), '#skF_4') | r1_xboole_0(A_230, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_4986])).
% 6.31/2.35  tff(c_5495, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_5479])).
% 6.31/2.35  tff(c_5502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_5495])).
% 6.31/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.35  
% 6.31/2.35  Inference rules
% 6.31/2.35  ----------------------
% 6.31/2.35  #Ref     : 0
% 6.31/2.35  #Sup     : 1185
% 6.31/2.35  #Fact    : 0
% 6.31/2.35  #Define  : 0
% 6.31/2.35  #Split   : 1
% 6.31/2.35  #Chain   : 0
% 6.31/2.35  #Close   : 0
% 6.31/2.35  
% 6.31/2.35  Ordering : KBO
% 6.31/2.35  
% 6.31/2.35  Simplification rules
% 6.31/2.35  ----------------------
% 6.31/2.35  #Subsume      : 144
% 6.31/2.35  #Demod        : 235
% 6.31/2.35  #Tautology    : 126
% 6.31/2.35  #SimpNegUnit  : 2
% 6.31/2.35  #BackRed      : 0
% 6.31/2.35  
% 6.31/2.35  #Partial instantiations: 0
% 6.31/2.35  #Strategies tried      : 1
% 6.31/2.35  
% 6.31/2.35  Timing (in seconds)
% 6.31/2.35  ----------------------
% 6.31/2.36  Preprocessing        : 0.30
% 6.31/2.36  Parsing              : 0.16
% 6.31/2.36  CNF conversion       : 0.02
% 6.31/2.36  Main loop            : 1.25
% 6.31/2.36  Inferencing          : 0.40
% 6.31/2.36  Reduction            : 0.36
% 6.31/2.36  Demodulation         : 0.27
% 6.31/2.36  BG Simplification    : 0.05
% 6.31/2.36  Subsumption          : 0.34
% 6.31/2.36  Abstraction          : 0.06
% 6.31/2.36  MUC search           : 0.00
% 6.31/2.36  Cooper               : 0.00
% 6.31/2.36  Total                : 1.58
% 6.31/2.36  Index Insertion      : 0.00
% 6.31/2.36  Index Deletion       : 0.00
% 6.31/2.36  Index Matching       : 0.00
% 6.31/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
