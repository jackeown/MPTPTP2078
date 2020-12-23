%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:03 EST 2020

% Result     : Theorem 13.08s
% Output     : CNFRefutation 13.08s
% Verified   : 
% Statistics : Number of formulae       :   60 (  92 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 182 expanded)
%              Number of equality atoms :   37 (  79 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_47,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_32,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_53,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_2'(A_33),A_33)
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [C_24] :
      ( C_24 = '#skF_4'
      | ~ r2_hidden(C_24,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_57,plain,
    ( '#skF_2'('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_53,c_28])).

tff(c_60,plain,(
    '#skF_2'('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_57])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_10])).

tff(c_67,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_64])).

tff(c_284,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_1'(A_58,B_59),B_59)
      | r1_xboole_0(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_290,plain,(
    ! [A_60] :
      ( '#skF_1'(A_60,'#skF_3') = '#skF_4'
      | r1_xboole_0(A_60,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_284,c_28])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden(A_19,B_20)
      | ~ r1_xboole_0(k1_tarski(A_19),B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_437,plain,(
    ! [A_70] :
      ( ~ r2_hidden(A_70,'#skF_3')
      | '#skF_1'(k1_tarski(A_70),'#skF_3') = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_290,c_24])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_446,plain,(
    ! [A_70] :
      ( r2_hidden('#skF_4',k1_tarski(A_70))
      | r1_xboole_0(k1_tarski(A_70),'#skF_3')
      | ~ r2_hidden(A_70,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_8])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_207,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_126,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_44)
      | r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_145,plain,(
    ! [B_48] :
      ( '#skF_1'('#skF_3',B_48) = '#skF_4'
      | r1_xboole_0('#skF_3',B_48) ) ),
    inference(resolution,[status(thm)],[c_126,c_28])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_151,plain,(
    ! [B_48] :
      ( k4_xboole_0('#skF_3',B_48) = '#skF_3'
      | '#skF_1'('#skF_3',B_48) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_145,c_16])).

tff(c_217,plain,(
    ! [B_54] :
      ( k3_xboole_0('#skF_3',B_54) = '#skF_3'
      | '#skF_1'('#skF_3',k4_xboole_0('#skF_3',B_54)) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_151])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_453,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,B_72)
      | ~ r2_hidden(C_73,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_490,plain,(
    ! [C_74,B_75,A_76] :
      ( ~ r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,k4_xboole_0(A_76,B_75)) ) ),
    inference(resolution,[status(thm)],[c_14,c_453])).

tff(c_3872,plain,(
    ! [A_172,A_173,B_174] :
      ( ~ r2_hidden('#skF_1'(A_172,k4_xboole_0(A_173,B_174)),B_174)
      | r1_xboole_0(A_172,k4_xboole_0(A_173,B_174)) ) ),
    inference(resolution,[status(thm)],[c_6,c_490])).

tff(c_23140,plain,(
    ! [B_394] :
      ( ~ r2_hidden('#skF_4',B_394)
      | r1_xboole_0('#skF_3',k4_xboole_0('#skF_3',B_394))
      | k3_xboole_0('#skF_3',B_394) = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_3872])).

tff(c_23145,plain,(
    ! [B_394] :
      ( k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',B_394)) = '#skF_3'
      | ~ r2_hidden('#skF_4',B_394)
      | k3_xboole_0('#skF_3',B_394) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_23140,c_16])).

tff(c_23220,plain,(
    ! [B_395] :
      ( k3_xboole_0('#skF_3',B_395) = '#skF_3'
      | ~ r2_hidden('#skF_4',B_395)
      | k3_xboole_0('#skF_3',B_395) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_23145])).

tff(c_45384,plain,(
    ! [A_472] :
      ( k3_xboole_0('#skF_3',k1_tarski(A_472)) = '#skF_3'
      | r1_xboole_0(k1_tarski(A_472),'#skF_3')
      | ~ r2_hidden(A_472,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_446,c_23220])).

tff(c_45399,plain,(
    ! [A_473] :
      ( k3_xboole_0('#skF_3',k1_tarski(A_473)) = '#skF_3'
      | ~ r2_hidden(A_473,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_45384,c_24])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( k3_xboole_0(B_22,k1_tarski(A_21)) = k1_tarski(A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_45709,plain,(
    ! [A_474] :
      ( k1_tarski(A_474) = '#skF_3'
      | ~ r2_hidden(A_474,'#skF_3')
      | ~ r2_hidden(A_474,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45399,c_26])).

tff(c_45717,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_45709])).

tff(c_45725,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_45717])).

tff(c_45727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_45725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.29  % Computer   : n025.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 15:34:35 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.08/6.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.08/6.52  
% 13.08/6.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.08/6.52  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 13.08/6.52  
% 13.08/6.52  %Foreground sorts:
% 13.08/6.52  
% 13.08/6.52  
% 13.08/6.52  %Background operators:
% 13.08/6.52  
% 13.08/6.52  
% 13.08/6.52  %Foreground operators:
% 13.08/6.52  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.08/6.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.08/6.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.08/6.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.08/6.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.08/6.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.08/6.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.08/6.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.08/6.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.08/6.52  tff('#skF_3', type, '#skF_3': $i).
% 13.08/6.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.08/6.52  tff('#skF_4', type, '#skF_4': $i).
% 13.08/6.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.08/6.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.08/6.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.08/6.52  
% 13.08/6.54  tff(f_91, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 13.08/6.54  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 13.08/6.54  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 13.08/6.54  tff(f_72, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 13.08/6.54  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.08/6.54  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.08/6.54  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 13.08/6.54  tff(f_76, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 13.08/6.54  tff(c_32, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.08/6.54  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.08/6.54  tff(c_53, plain, (![A_33]: (r2_hidden('#skF_2'(A_33), A_33) | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.08/6.54  tff(c_28, plain, (![C_24]: (C_24='#skF_4' | ~r2_hidden(C_24, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.08/6.54  tff(c_57, plain, ('#skF_2'('#skF_3')='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_53, c_28])).
% 13.08/6.54  tff(c_60, plain, ('#skF_2'('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_30, c_57])).
% 13.08/6.54  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.08/6.54  tff(c_64, plain, (r2_hidden('#skF_4', '#skF_3') | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_60, c_10])).
% 13.08/6.54  tff(c_67, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_64])).
% 13.08/6.54  tff(c_284, plain, (![A_58, B_59]: (r2_hidden('#skF_1'(A_58, B_59), B_59) | r1_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.08/6.54  tff(c_290, plain, (![A_60]: ('#skF_1'(A_60, '#skF_3')='#skF_4' | r1_xboole_0(A_60, '#skF_3'))), inference(resolution, [status(thm)], [c_284, c_28])).
% 13.08/6.54  tff(c_24, plain, (![A_19, B_20]: (~r2_hidden(A_19, B_20) | ~r1_xboole_0(k1_tarski(A_19), B_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.08/6.54  tff(c_437, plain, (![A_70]: (~r2_hidden(A_70, '#skF_3') | '#skF_1'(k1_tarski(A_70), '#skF_3')='#skF_4')), inference(resolution, [status(thm)], [c_290, c_24])).
% 13.08/6.54  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.08/6.54  tff(c_446, plain, (![A_70]: (r2_hidden('#skF_4', k1_tarski(A_70)) | r1_xboole_0(k1_tarski(A_70), '#skF_3') | ~r2_hidden(A_70, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_437, c_8])).
% 13.08/6.54  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.08/6.54  tff(c_207, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.08/6.54  tff(c_126, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), A_44) | r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.08/6.54  tff(c_145, plain, (![B_48]: ('#skF_1'('#skF_3', B_48)='#skF_4' | r1_xboole_0('#skF_3', B_48))), inference(resolution, [status(thm)], [c_126, c_28])).
% 13.08/6.54  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.08/6.54  tff(c_151, plain, (![B_48]: (k4_xboole_0('#skF_3', B_48)='#skF_3' | '#skF_1'('#skF_3', B_48)='#skF_4')), inference(resolution, [status(thm)], [c_145, c_16])).
% 13.08/6.54  tff(c_217, plain, (![B_54]: (k3_xboole_0('#skF_3', B_54)='#skF_3' | '#skF_1'('#skF_3', k4_xboole_0('#skF_3', B_54))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_207, c_151])).
% 13.08/6.54  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.08/6.54  tff(c_14, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.08/6.54  tff(c_453, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, B_72) | ~r2_hidden(C_73, A_71))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.08/6.54  tff(c_490, plain, (![C_74, B_75, A_76]: (~r2_hidden(C_74, B_75) | ~r2_hidden(C_74, k4_xboole_0(A_76, B_75)))), inference(resolution, [status(thm)], [c_14, c_453])).
% 13.08/6.54  tff(c_3872, plain, (![A_172, A_173, B_174]: (~r2_hidden('#skF_1'(A_172, k4_xboole_0(A_173, B_174)), B_174) | r1_xboole_0(A_172, k4_xboole_0(A_173, B_174)))), inference(resolution, [status(thm)], [c_6, c_490])).
% 13.08/6.54  tff(c_23140, plain, (![B_394]: (~r2_hidden('#skF_4', B_394) | r1_xboole_0('#skF_3', k4_xboole_0('#skF_3', B_394)) | k3_xboole_0('#skF_3', B_394)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_217, c_3872])).
% 13.08/6.54  tff(c_23145, plain, (![B_394]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', B_394))='#skF_3' | ~r2_hidden('#skF_4', B_394) | k3_xboole_0('#skF_3', B_394)='#skF_3')), inference(resolution, [status(thm)], [c_23140, c_16])).
% 13.08/6.54  tff(c_23220, plain, (![B_395]: (k3_xboole_0('#skF_3', B_395)='#skF_3' | ~r2_hidden('#skF_4', B_395) | k3_xboole_0('#skF_3', B_395)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_23145])).
% 13.08/6.54  tff(c_45384, plain, (![A_472]: (k3_xboole_0('#skF_3', k1_tarski(A_472))='#skF_3' | r1_xboole_0(k1_tarski(A_472), '#skF_3') | ~r2_hidden(A_472, '#skF_3'))), inference(resolution, [status(thm)], [c_446, c_23220])).
% 13.08/6.54  tff(c_45399, plain, (![A_473]: (k3_xboole_0('#skF_3', k1_tarski(A_473))='#skF_3' | ~r2_hidden(A_473, '#skF_3'))), inference(resolution, [status(thm)], [c_45384, c_24])).
% 13.08/6.54  tff(c_26, plain, (![B_22, A_21]: (k3_xboole_0(B_22, k1_tarski(A_21))=k1_tarski(A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.08/6.54  tff(c_45709, plain, (![A_474]: (k1_tarski(A_474)='#skF_3' | ~r2_hidden(A_474, '#skF_3') | ~r2_hidden(A_474, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_45399, c_26])).
% 13.08/6.54  tff(c_45717, plain, (k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_67, c_45709])).
% 13.08/6.54  tff(c_45725, plain, (k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_45717])).
% 13.08/6.54  tff(c_45727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_45725])).
% 13.08/6.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.08/6.54  
% 13.08/6.54  Inference rules
% 13.08/6.54  ----------------------
% 13.08/6.54  #Ref     : 0
% 13.08/6.54  #Sup     : 11090
% 13.08/6.54  #Fact    : 0
% 13.08/6.54  #Define  : 0
% 13.08/6.54  #Split   : 0
% 13.08/6.54  #Chain   : 0
% 13.08/6.54  #Close   : 0
% 13.08/6.54  
% 13.08/6.54  Ordering : KBO
% 13.08/6.54  
% 13.08/6.54  Simplification rules
% 13.08/6.54  ----------------------
% 13.08/6.54  #Subsume      : 3217
% 13.08/6.54  #Demod        : 13518
% 13.08/6.54  #Tautology    : 3823
% 13.08/6.54  #SimpNegUnit  : 452
% 13.08/6.54  #BackRed      : 4
% 13.08/6.54  
% 13.08/6.54  #Partial instantiations: 0
% 13.08/6.54  #Strategies tried      : 1
% 13.08/6.54  
% 13.08/6.54  Timing (in seconds)
% 13.08/6.54  ----------------------
% 13.08/6.54  Preprocessing        : 0.30
% 13.08/6.54  Parsing              : 0.16
% 13.08/6.54  CNF conversion       : 0.02
% 13.08/6.54  Main loop            : 5.58
% 13.08/6.54  Inferencing          : 0.99
% 13.08/6.54  Reduction            : 2.03
% 13.08/6.54  Demodulation         : 1.59
% 13.08/6.54  BG Simplification    : 0.13
% 13.08/6.54  Subsumption          : 2.14
% 13.08/6.54  Abstraction          : 0.21
% 13.08/6.54  MUC search           : 0.00
% 13.08/6.54  Cooper               : 0.00
% 13.08/6.54  Total                : 5.91
% 13.08/6.54  Index Insertion      : 0.00
% 13.08/6.54  Index Deletion       : 0.00
% 13.08/6.54  Index Matching       : 0.00
% 13.08/6.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
