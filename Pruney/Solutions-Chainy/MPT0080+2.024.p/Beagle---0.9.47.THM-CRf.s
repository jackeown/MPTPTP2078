%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:52 EST 2020

% Result     : Theorem 42.75s
% Output     : CNFRefutation 42.75s
% Verified   : 
% Statistics : Number of formulae       :   62 (  82 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 179 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_66,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_48,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,k4_xboole_0(A_8,B_9))
      | r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_4'(A_16,B_17),A_16)
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_4'(A_16,B_17),B_17)
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_138,plain,(
    ! [D_48,B_49,A_50] :
      ( ~ r2_hidden(D_48,B_49)
      | ~ r2_hidden(D_48,k4_xboole_0(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4227,plain,(
    ! [A_214,A_215,B_216] :
      ( ~ r2_hidden('#skF_4'(A_214,k4_xboole_0(A_215,B_216)),B_216)
      | r1_xboole_0(A_214,k4_xboole_0(A_215,B_216)) ) ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_4248,plain,(
    ! [A_217,A_218] : r1_xboole_0(A_217,k4_xboole_0(A_218,A_217)) ),
    inference(resolution,[status(thm)],[c_34,c_4227])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( r1_xboole_0(B_15,A_14)
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4254,plain,(
    ! [A_218,A_217] : r1_xboole_0(k4_xboole_0(A_218,A_217),A_217) ),
    inference(resolution,[status(thm)],[c_4248,c_28])).

tff(c_240,plain,(
    ! [A_61,B_62] :
      ( ~ r2_hidden('#skF_1'(A_61,B_62),B_62)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_245,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_240])).

tff(c_229,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_4'(A_59,B_60),A_59)
      | r1_xboole_0(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_5311,plain,(
    ! [A_276,B_277,B_278] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_276,B_277),B_278),A_276)
      | r1_xboole_0(k4_xboole_0(A_276,B_277),B_278) ) ),
    inference(resolution,[status(thm)],[c_229,c_14])).

tff(c_390,plain,(
    ! [C_73,B_74,A_75] :
      ( r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3927,plain,(
    ! [A_198,B_199,B_200] :
      ( r2_hidden('#skF_4'(A_198,B_199),B_200)
      | ~ r1_tarski(B_199,B_200)
      | r1_xboole_0(A_198,B_199) ) ),
    inference(resolution,[status(thm)],[c_32,c_390])).

tff(c_50,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_633,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,B_84)
      | ~ r2_hidden(C_85,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_639,plain,(
    ! [C_85] :
      ( ~ r2_hidden(C_85,'#skF_7')
      | ~ r2_hidden(C_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_633])).

tff(c_3957,plain,(
    ! [A_198,B_199] :
      ( ~ r2_hidden('#skF_4'(A_198,B_199),'#skF_5')
      | ~ r1_tarski(B_199,'#skF_7')
      | r1_xboole_0(A_198,B_199) ) ),
    inference(resolution,[status(thm)],[c_3927,c_639])).

tff(c_6417,plain,(
    ! [B_303,B_304] :
      ( ~ r1_tarski(B_303,'#skF_7')
      | r1_xboole_0(k4_xboole_0('#skF_5',B_304),B_303) ) ),
    inference(resolution,[status(thm)],[c_5311,c_3957])).

tff(c_899,plain,(
    ! [A_94,C_95,B_96] :
      ( ~ r1_xboole_0(A_94,C_95)
      | ~ r1_xboole_0(A_94,B_96)
      | r1_xboole_0(A_94,k2_xboole_0(B_96,C_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    r1_tarski('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_111,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_123,plain,(
    k2_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) = k2_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_111])).

tff(c_44,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_xboole_0(A_25,B_26)
      | ~ r1_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_214,plain,(
    ! [A_25] :
      ( r1_xboole_0(A_25,'#skF_5')
      | ~ r1_xboole_0(A_25,k2_xboole_0('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_44])).

tff(c_948,plain,(
    ! [A_94] :
      ( r1_xboole_0(A_94,'#skF_5')
      | ~ r1_xboole_0(A_94,'#skF_7')
      | ~ r1_xboole_0(A_94,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_899,c_214])).

tff(c_6425,plain,(
    ! [B_304] :
      ( r1_xboole_0(k4_xboole_0('#skF_5',B_304),'#skF_5')
      | ~ r1_xboole_0(k4_xboole_0('#skF_5',B_304),'#skF_6')
      | ~ r1_tarski('#skF_7','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6417,c_948])).

tff(c_121261,plain,(
    ! [B_2050] :
      ( r1_xboole_0(k4_xboole_0('#skF_5',B_2050),'#skF_5')
      | ~ r1_xboole_0(k4_xboole_0('#skF_5',B_2050),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_6425])).

tff(c_121450,plain,(
    ! [B_2055] :
      ( r1_xboole_0('#skF_5',k4_xboole_0('#skF_5',B_2055))
      | ~ r1_xboole_0(k4_xboole_0('#skF_5',B_2055),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_121261,c_28])).

tff(c_121647,plain,(
    r1_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4254,c_121450])).

tff(c_30,plain,(
    ! [A_16,B_17,C_20] :
      ( ~ r1_xboole_0(A_16,B_17)
      | ~ r2_hidden(C_20,B_17)
      | ~ r2_hidden(C_20,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_126165,plain,(
    ! [C_2123] :
      ( ~ r2_hidden(C_2123,k4_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_2123,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_121647,c_30])).

tff(c_126688,plain,(
    ! [D_2124] :
      ( r2_hidden(D_2124,'#skF_6')
      | ~ r2_hidden(D_2124,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_126165])).

tff(c_127937,plain,(
    ! [B_2140] :
      ( r2_hidden('#skF_1'('#skF_5',B_2140),'#skF_6')
      | r1_tarski('#skF_5',B_2140) ) ),
    inference(resolution,[status(thm)],[c_8,c_126688])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_127961,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_127937,c_6])).

tff(c_127979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_127961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:56:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 42.75/32.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.75/32.56  
% 42.75/32.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.75/32.56  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 42.75/32.56  
% 42.75/32.56  %Foreground sorts:
% 42.75/32.56  
% 42.75/32.56  
% 42.75/32.56  %Background operators:
% 42.75/32.56  
% 42.75/32.56  
% 42.75/32.56  %Foreground operators:
% 42.75/32.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 42.75/32.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 42.75/32.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 42.75/32.56  tff('#skF_7', type, '#skF_7': $i).
% 42.75/32.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 42.75/32.56  tff('#skF_5', type, '#skF_5': $i).
% 42.75/32.56  tff('#skF_6', type, '#skF_6': $i).
% 42.75/32.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 42.75/32.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 42.75/32.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 42.75/32.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 42.75/32.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 42.75/32.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 42.75/32.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 42.75/32.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 42.75/32.56  
% 42.75/32.58  tff(f_97, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 42.75/32.58  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 42.75/32.58  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 42.75/32.58  tff(f_66, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 42.75/32.58  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 42.75/32.58  tff(f_88, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 42.75/32.58  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 42.75/32.58  tff(c_48, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 42.75/32.58  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 42.75/32.58  tff(c_10, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, k4_xboole_0(A_8, B_9)) | r2_hidden(D_13, B_9) | ~r2_hidden(D_13, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 42.75/32.58  tff(c_34, plain, (![A_16, B_17]: (r2_hidden('#skF_4'(A_16, B_17), A_16) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 42.75/32.58  tff(c_32, plain, (![A_16, B_17]: (r2_hidden('#skF_4'(A_16, B_17), B_17) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 42.75/32.58  tff(c_138, plain, (![D_48, B_49, A_50]: (~r2_hidden(D_48, B_49) | ~r2_hidden(D_48, k4_xboole_0(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 42.75/32.58  tff(c_4227, plain, (![A_214, A_215, B_216]: (~r2_hidden('#skF_4'(A_214, k4_xboole_0(A_215, B_216)), B_216) | r1_xboole_0(A_214, k4_xboole_0(A_215, B_216)))), inference(resolution, [status(thm)], [c_32, c_138])).
% 42.75/32.58  tff(c_4248, plain, (![A_217, A_218]: (r1_xboole_0(A_217, k4_xboole_0(A_218, A_217)))), inference(resolution, [status(thm)], [c_34, c_4227])).
% 42.75/32.58  tff(c_28, plain, (![B_15, A_14]: (r1_xboole_0(B_15, A_14) | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 42.75/32.58  tff(c_4254, plain, (![A_218, A_217]: (r1_xboole_0(k4_xboole_0(A_218, A_217), A_217))), inference(resolution, [status(thm)], [c_4248, c_28])).
% 42.75/32.58  tff(c_240, plain, (![A_61, B_62]: (~r2_hidden('#skF_1'(A_61, B_62), B_62) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_34])).
% 42.75/32.58  tff(c_245, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_240])).
% 42.75/32.58  tff(c_229, plain, (![A_59, B_60]: (r2_hidden('#skF_4'(A_59, B_60), A_59) | r1_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_66])).
% 42.75/32.58  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 42.75/32.58  tff(c_5311, plain, (![A_276, B_277, B_278]: (r2_hidden('#skF_4'(k4_xboole_0(A_276, B_277), B_278), A_276) | r1_xboole_0(k4_xboole_0(A_276, B_277), B_278))), inference(resolution, [status(thm)], [c_229, c_14])).
% 42.75/32.58  tff(c_390, plain, (![C_73, B_74, A_75]: (r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_34])).
% 42.75/32.58  tff(c_3927, plain, (![A_198, B_199, B_200]: (r2_hidden('#skF_4'(A_198, B_199), B_200) | ~r1_tarski(B_199, B_200) | r1_xboole_0(A_198, B_199))), inference(resolution, [status(thm)], [c_32, c_390])).
% 42.75/32.58  tff(c_50, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_97])).
% 42.75/32.58  tff(c_633, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, B_84) | ~r2_hidden(C_85, A_83))), inference(cnfTransformation, [status(thm)], [f_66])).
% 42.75/32.58  tff(c_639, plain, (![C_85]: (~r2_hidden(C_85, '#skF_7') | ~r2_hidden(C_85, '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_633])).
% 42.75/32.58  tff(c_3957, plain, (![A_198, B_199]: (~r2_hidden('#skF_4'(A_198, B_199), '#skF_5') | ~r1_tarski(B_199, '#skF_7') | r1_xboole_0(A_198, B_199))), inference(resolution, [status(thm)], [c_3927, c_639])).
% 42.75/32.58  tff(c_6417, plain, (![B_303, B_304]: (~r1_tarski(B_303, '#skF_7') | r1_xboole_0(k4_xboole_0('#skF_5', B_304), B_303))), inference(resolution, [status(thm)], [c_5311, c_3957])).
% 42.75/32.58  tff(c_899, plain, (![A_94, C_95, B_96]: (~r1_xboole_0(A_94, C_95) | ~r1_xboole_0(A_94, B_96) | r1_xboole_0(A_94, k2_xboole_0(B_96, C_95)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 42.75/32.58  tff(c_52, plain, (r1_tarski('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 42.75/32.58  tff(c_111, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_70])).
% 42.75/32.58  tff(c_123, plain, (k2_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))=k2_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_111])).
% 42.75/32.58  tff(c_44, plain, (![A_25, B_26, C_27]: (r1_xboole_0(A_25, B_26) | ~r1_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 42.75/32.58  tff(c_214, plain, (![A_25]: (r1_xboole_0(A_25, '#skF_5') | ~r1_xboole_0(A_25, k2_xboole_0('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_123, c_44])).
% 42.75/32.58  tff(c_948, plain, (![A_94]: (r1_xboole_0(A_94, '#skF_5') | ~r1_xboole_0(A_94, '#skF_7') | ~r1_xboole_0(A_94, '#skF_6'))), inference(resolution, [status(thm)], [c_899, c_214])).
% 42.75/32.58  tff(c_6425, plain, (![B_304]: (r1_xboole_0(k4_xboole_0('#skF_5', B_304), '#skF_5') | ~r1_xboole_0(k4_xboole_0('#skF_5', B_304), '#skF_6') | ~r1_tarski('#skF_7', '#skF_7'))), inference(resolution, [status(thm)], [c_6417, c_948])).
% 42.75/32.58  tff(c_121261, plain, (![B_2050]: (r1_xboole_0(k4_xboole_0('#skF_5', B_2050), '#skF_5') | ~r1_xboole_0(k4_xboole_0('#skF_5', B_2050), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_245, c_6425])).
% 42.75/32.58  tff(c_121450, plain, (![B_2055]: (r1_xboole_0('#skF_5', k4_xboole_0('#skF_5', B_2055)) | ~r1_xboole_0(k4_xboole_0('#skF_5', B_2055), '#skF_6'))), inference(resolution, [status(thm)], [c_121261, c_28])).
% 42.75/32.58  tff(c_121647, plain, (r1_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_4254, c_121450])).
% 42.75/32.58  tff(c_30, plain, (![A_16, B_17, C_20]: (~r1_xboole_0(A_16, B_17) | ~r2_hidden(C_20, B_17) | ~r2_hidden(C_20, A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 42.75/32.58  tff(c_126165, plain, (![C_2123]: (~r2_hidden(C_2123, k4_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(C_2123, '#skF_5'))), inference(resolution, [status(thm)], [c_121647, c_30])).
% 42.75/32.58  tff(c_126688, plain, (![D_2124]: (r2_hidden(D_2124, '#skF_6') | ~r2_hidden(D_2124, '#skF_5'))), inference(resolution, [status(thm)], [c_10, c_126165])).
% 42.75/32.58  tff(c_127937, plain, (![B_2140]: (r2_hidden('#skF_1'('#skF_5', B_2140), '#skF_6') | r1_tarski('#skF_5', B_2140))), inference(resolution, [status(thm)], [c_8, c_126688])).
% 42.75/32.58  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 42.75/32.58  tff(c_127961, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_127937, c_6])).
% 42.75/32.58  tff(c_127979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_127961])).
% 42.75/32.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 42.75/32.58  
% 42.75/32.58  Inference rules
% 42.75/32.58  ----------------------
% 42.75/32.58  #Ref     : 0
% 42.75/32.58  #Sup     : 32186
% 42.75/32.58  #Fact    : 2
% 42.75/32.58  #Define  : 0
% 42.75/32.58  #Split   : 10
% 42.75/32.58  #Chain   : 0
% 42.75/32.58  #Close   : 0
% 42.75/32.58  
% 42.75/32.58  Ordering : KBO
% 42.75/32.58  
% 42.75/32.58  Simplification rules
% 42.75/32.58  ----------------------
% 42.75/32.58  #Subsume      : 6967
% 42.75/32.58  #Demod        : 25851
% 42.75/32.58  #Tautology    : 12053
% 42.75/32.58  #SimpNegUnit  : 71
% 42.75/32.58  #BackRed      : 10
% 42.75/32.58  
% 42.75/32.58  #Partial instantiations: 0
% 42.75/32.58  #Strategies tried      : 1
% 42.75/32.58  
% 42.75/32.58  Timing (in seconds)
% 42.75/32.58  ----------------------
% 42.75/32.58  Preprocessing        : 0.28
% 42.75/32.58  Parsing              : 0.15
% 42.75/32.58  CNF conversion       : 0.02
% 42.75/32.58  Main loop            : 31.53
% 42.75/32.58  Inferencing          : 2.81
% 42.75/32.58  Reduction            : 13.96
% 42.75/32.58  Demodulation         : 12.08
% 42.75/32.58  BG Simplification    : 0.32
% 42.75/32.58  Subsumption          : 13.10
% 42.75/32.58  Abstraction          : 0.51
% 42.75/32.58  MUC search           : 0.00
% 42.75/32.58  Cooper               : 0.00
% 42.75/32.58  Total                : 31.84
% 42.75/32.58  Index Insertion      : 0.00
% 42.75/32.58  Index Deletion       : 0.00
% 42.75/32.58  Index Matching       : 0.00
% 42.75/32.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
