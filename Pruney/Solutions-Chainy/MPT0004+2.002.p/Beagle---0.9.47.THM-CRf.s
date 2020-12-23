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
% DateTime   : Thu Dec  3 09:42:27 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   57 (  98 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   78 ( 210 expanded)
%              Number of equality atoms :    1 (   6 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ ( ~ r1_xboole_0(A,B)
            & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
        & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_30,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_33,plain,(
    ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_226,plain,(
    ! [D_55,A_56,B_57] :
      ( r2_hidden(D_55,k3_xboole_0(A_56,B_57))
      | ~ r2_hidden(D_55,B_57)
      | ~ r2_hidden(D_55,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    ! [C_14] :
      ( r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_5'))
      | ~ r2_hidden(C_14,k3_xboole_0('#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_158,plain,(
    ! [C_14] : ~ r2_hidden(C_14,k3_xboole_0('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_240,plain,(
    ! [D_58] :
      ( ~ r2_hidden(D_58,'#skF_8')
      | ~ r2_hidden(D_58,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_226,c_158])).

tff(c_260,plain,(
    ! [B_60] :
      ( ~ r2_hidden('#skF_3'('#skF_7',B_60),'#skF_8')
      | r1_xboole_0('#skF_7',B_60) ) ),
    inference(resolution,[status(thm)],[c_24,c_240])).

tff(c_264,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_22,c_260])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_33,c_264])).

tff(c_269,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_274,plain,(
    ! [D_61,A_62,B_63] :
      ( r2_hidden(D_61,A_62)
      | ~ r2_hidden(D_61,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_282,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_269,c_274])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_273,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_269,c_4])).

tff(c_79,plain,(
    ! [D_31,A_32,B_33] :
      ( r2_hidden(D_31,k3_xboole_0(A_32,B_33))
      | ~ r2_hidden(D_31,B_33)
      | ~ r2_hidden(D_31,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [C_14] :
      ( r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_14,k3_xboole_0('#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_35,plain,(
    ! [C_14] : ~ r2_hidden(C_14,k3_xboole_0('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_93,plain,(
    ! [D_34] :
      ( ~ r2_hidden(D_34,'#skF_8')
      | ~ r2_hidden(D_34,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_79,c_35])).

tff(c_142,plain,(
    ! [B_38] :
      ( ~ r2_hidden('#skF_3'('#skF_7',B_38),'#skF_8')
      | r1_xboole_0('#skF_7',B_38) ) ),
    inference(resolution,[status(thm)],[c_24,c_93])).

tff(c_146,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_33,c_146])).

tff(c_151,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_295,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,B_67)
      | ~ r2_hidden(C_68,A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_299,plain,(
    ! [C_69] :
      ( ~ r2_hidden(C_69,'#skF_5')
      | ~ r2_hidden(C_69,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_151,c_295])).

tff(c_306,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_273,c_299])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_306])).

tff(c_317,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_5'))
    | ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_319,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_32])).

tff(c_331,plain,(
    ! [D_75,A_76,B_77] :
      ( r2_hidden(D_75,A_76)
      | ~ r2_hidden(D_75,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_340,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_319,c_331])).

tff(c_320,plain,(
    ! [D_70,B_71,A_72] :
      ( r2_hidden(D_70,B_71)
      | ~ r2_hidden(D_70,k3_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_324,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_319,c_320])).

tff(c_316,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_353,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | ~ r2_hidden(C_82,B_81)
      | ~ r2_hidden(C_82,A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_371,plain,(
    ! [C_84] :
      ( ~ r2_hidden(C_84,'#skF_5')
      | ~ r2_hidden(C_84,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_316,c_353])).

tff(c_382,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_324,c_371])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.39  
% 2.19/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.39  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 2.19/1.39  
% 2.19/1.39  %Foreground sorts:
% 2.19/1.39  
% 2.19/1.39  
% 2.19/1.39  %Background operators:
% 2.19/1.39  
% 2.19/1.39  
% 2.19/1.39  %Foreground operators:
% 2.19/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.19/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.19/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.39  
% 2.38/1.40  tff(f_67, negated_conjecture, ~(![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.38/1.40  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.38/1.40  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.38/1.40  tff(c_30, plain, (r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.40  tff(c_33, plain, (~r1_xboole_0('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_30])).
% 2.38/1.40  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.38/1.40  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.38/1.40  tff(c_226, plain, (![D_55, A_56, B_57]: (r2_hidden(D_55, k3_xboole_0(A_56, B_57)) | ~r2_hidden(D_55, B_57) | ~r2_hidden(D_55, A_56))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.40  tff(c_28, plain, (![C_14]: (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_5')) | ~r2_hidden(C_14, k3_xboole_0('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.40  tff(c_158, plain, (![C_14]: (~r2_hidden(C_14, k3_xboole_0('#skF_7', '#skF_8')))), inference(splitLeft, [status(thm)], [c_28])).
% 2.38/1.40  tff(c_240, plain, (![D_58]: (~r2_hidden(D_58, '#skF_8') | ~r2_hidden(D_58, '#skF_7'))), inference(resolution, [status(thm)], [c_226, c_158])).
% 2.38/1.40  tff(c_260, plain, (![B_60]: (~r2_hidden('#skF_3'('#skF_7', B_60), '#skF_8') | r1_xboole_0('#skF_7', B_60))), inference(resolution, [status(thm)], [c_24, c_240])).
% 2.38/1.40  tff(c_264, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_22, c_260])).
% 2.38/1.40  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_33, c_264])).
% 2.38/1.40  tff(c_269, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_28])).
% 2.38/1.40  tff(c_274, plain, (![D_61, A_62, B_63]: (r2_hidden(D_61, A_62) | ~r2_hidden(D_61, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.40  tff(c_282, plain, (r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_269, c_274])).
% 2.38/1.40  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.40  tff(c_273, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_269, c_4])).
% 2.38/1.40  tff(c_79, plain, (![D_31, A_32, B_33]: (r2_hidden(D_31, k3_xboole_0(A_32, B_33)) | ~r2_hidden(D_31, B_33) | ~r2_hidden(D_31, A_32))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.40  tff(c_26, plain, (![C_14]: (r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_14, k3_xboole_0('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.40  tff(c_35, plain, (![C_14]: (~r2_hidden(C_14, k3_xboole_0('#skF_7', '#skF_8')))), inference(splitLeft, [status(thm)], [c_26])).
% 2.38/1.40  tff(c_93, plain, (![D_34]: (~r2_hidden(D_34, '#skF_8') | ~r2_hidden(D_34, '#skF_7'))), inference(resolution, [status(thm)], [c_79, c_35])).
% 2.38/1.40  tff(c_142, plain, (![B_38]: (~r2_hidden('#skF_3'('#skF_7', B_38), '#skF_8') | r1_xboole_0('#skF_7', B_38))), inference(resolution, [status(thm)], [c_24, c_93])).
% 2.38/1.40  tff(c_146, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_22, c_142])).
% 2.38/1.40  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_33, c_146])).
% 2.38/1.40  tff(c_151, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 2.38/1.40  tff(c_295, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, B_67) | ~r2_hidden(C_68, A_66))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.38/1.40  tff(c_299, plain, (![C_69]: (~r2_hidden(C_69, '#skF_5') | ~r2_hidden(C_69, '#skF_4'))), inference(resolution, [status(thm)], [c_151, c_295])).
% 2.38/1.40  tff(c_306, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_273, c_299])).
% 2.38/1.40  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_282, c_306])).
% 2.38/1.40  tff(c_317, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_30])).
% 2.38/1.40  tff(c_32, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_5')) | ~r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.40  tff(c_319, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_32])).
% 2.38/1.40  tff(c_331, plain, (![D_75, A_76, B_77]: (r2_hidden(D_75, A_76) | ~r2_hidden(D_75, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.40  tff(c_340, plain, (r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_319, c_331])).
% 2.38/1.40  tff(c_320, plain, (![D_70, B_71, A_72]: (r2_hidden(D_70, B_71) | ~r2_hidden(D_70, k3_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.40  tff(c_324, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_319, c_320])).
% 2.38/1.40  tff(c_316, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_30])).
% 2.38/1.40  tff(c_353, plain, (![A_80, B_81, C_82]: (~r1_xboole_0(A_80, B_81) | ~r2_hidden(C_82, B_81) | ~r2_hidden(C_82, A_80))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.38/1.40  tff(c_371, plain, (![C_84]: (~r2_hidden(C_84, '#skF_5') | ~r2_hidden(C_84, '#skF_4'))), inference(resolution, [status(thm)], [c_316, c_353])).
% 2.38/1.40  tff(c_382, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_324, c_371])).
% 2.38/1.40  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_340, c_382])).
% 2.38/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.40  
% 2.38/1.40  Inference rules
% 2.38/1.40  ----------------------
% 2.38/1.40  #Ref     : 0
% 2.38/1.40  #Sup     : 65
% 2.38/1.40  #Fact    : 0
% 2.38/1.40  #Define  : 0
% 2.38/1.40  #Split   : 3
% 2.38/1.40  #Chain   : 0
% 2.38/1.40  #Close   : 0
% 2.38/1.40  
% 2.38/1.40  Ordering : KBO
% 2.38/1.40  
% 2.38/1.40  Simplification rules
% 2.38/1.40  ----------------------
% 2.38/1.41  #Subsume      : 8
% 2.38/1.41  #Demod        : 5
% 2.38/1.41  #Tautology    : 6
% 2.38/1.41  #SimpNegUnit  : 2
% 2.38/1.41  #BackRed      : 0
% 2.38/1.41  
% 2.38/1.41  #Partial instantiations: 0
% 2.38/1.41  #Strategies tried      : 1
% 2.38/1.41  
% 2.38/1.41  Timing (in seconds)
% 2.38/1.41  ----------------------
% 2.38/1.41  Preprocessing        : 0.36
% 2.38/1.41  Parsing              : 0.19
% 2.38/1.41  CNF conversion       : 0.03
% 2.38/1.41  Main loop            : 0.25
% 2.38/1.41  Inferencing          : 0.11
% 2.38/1.41  Reduction            : 0.05
% 2.38/1.41  Demodulation         : 0.03
% 2.38/1.41  BG Simplification    : 0.02
% 2.38/1.41  Subsumption          : 0.05
% 2.38/1.41  Abstraction          : 0.01
% 2.38/1.41  MUC search           : 0.00
% 2.38/1.41  Cooper               : 0.00
% 2.38/1.41  Total                : 0.65
% 2.38/1.41  Index Insertion      : 0.00
% 2.38/1.41  Index Deletion       : 0.00
% 2.38/1.41  Index Matching       : 0.00
% 2.38/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
