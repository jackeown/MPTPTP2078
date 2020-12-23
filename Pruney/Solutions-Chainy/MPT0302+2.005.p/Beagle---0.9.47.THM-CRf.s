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
% DateTime   : Thu Dec  3 09:53:47 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 111 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 192 expanded)
%              Number of equality atoms :   23 (  65 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_28,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_225,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( r2_hidden(k4_tarski(A_57,B_58),k2_zfmisc_1(C_59,D_60))
      | ~ r2_hidden(B_58,D_60)
      | ~ r2_hidden(A_57,C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    k2_zfmisc_1('#skF_5','#skF_4') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_184,plain,(
    ! [A_38,C_39,B_40,D_41] :
      ( r2_hidden(A_38,C_39)
      | ~ r2_hidden(k4_tarski(A_38,B_40),k2_zfmisc_1(C_39,D_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_187,plain,(
    ! [A_38,B_40] :
      ( r2_hidden(A_38,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_38,B_40),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_184])).

tff(c_245,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,'#skF_5')
      | ~ r2_hidden(B_58,'#skF_5')
      | ~ r2_hidden(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_225,c_187])).

tff(c_252,plain,(
    ! [B_61] : ~ r2_hidden(B_61,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_275,plain,(
    ! [B_62] : r1_tarski('#skF_5',B_62) ),
    inference(resolution,[status(thm)],[c_8,c_252])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_280,plain,(
    ! [B_63] : k3_xboole_0('#skF_5',B_63) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_275,c_18])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    ! [A_23] : k3_xboole_0(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_73])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_83,plain,(
    ! [A_23] : k3_xboole_0(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2])).

tff(c_289,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_83])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_289])).

tff(c_318,plain,(
    ! [A_64] :
      ( r2_hidden(A_64,'#skF_5')
      | ~ r2_hidden(A_64,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_336,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_65,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_318,c_6])).

tff(c_346,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_336])).

tff(c_350,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_346,c_18])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_180,plain,(
    ! [B_34,D_35,A_36,C_37] :
      ( r2_hidden(B_34,D_35)
      | ~ r2_hidden(k4_tarski(A_36,B_34),k2_zfmisc_1(C_37,D_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_183,plain,(
    ! [B_34,A_36] :
      ( r2_hidden(B_34,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_36,B_34),k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_180])).

tff(c_246,plain,(
    ! [B_58,A_57] :
      ( r2_hidden(B_58,'#skF_4')
      | ~ r2_hidden(B_58,'#skF_5')
      | ~ r2_hidden(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_225,c_183])).

tff(c_395,plain,(
    ! [A_70] : ~ r2_hidden(A_70,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_419,plain,(
    ! [B_71] : r1_tarski('#skF_4',B_71) ),
    inference(resolution,[status(thm)],[c_8,c_395])).

tff(c_431,plain,(
    ! [B_72] : k3_xboole_0('#skF_4',B_72) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_419,c_18])).

tff(c_440,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_83])).

tff(c_467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_440])).

tff(c_469,plain,(
    ! [B_73] :
      ( r2_hidden(B_73,'#skF_4')
      | ~ r2_hidden(B_73,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_496,plain,(
    ! [B_74] :
      ( r2_hidden('#skF_1'('#skF_5',B_74),'#skF_4')
      | r1_tarski('#skF_5',B_74) ) ),
    inference(resolution,[status(thm)],[c_8,c_469])).

tff(c_510,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_496,c_6])).

tff(c_542,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_510,c_18])).

tff(c_546,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_2])).

tff(c_558,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_546])).

tff(c_560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_558])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.32  
% 2.43/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.32  %$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.43/1.32  
% 2.43/1.32  %Foreground sorts:
% 2.43/1.32  
% 2.43/1.32  
% 2.43/1.32  %Background operators:
% 2.43/1.32  
% 2.43/1.32  
% 2.43/1.32  %Foreground operators:
% 2.43/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.43/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.43/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.43/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.32  
% 2.43/1.34  tff(f_62, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.43/1.34  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.43/1.34  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.43/1.34  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.43/1.34  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.43/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.43/1.34  tff(c_28, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.43/1.34  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.43/1.34  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.43/1.34  tff(c_225, plain, (![A_57, B_58, C_59, D_60]: (r2_hidden(k4_tarski(A_57, B_58), k2_zfmisc_1(C_59, D_60)) | ~r2_hidden(B_58, D_60) | ~r2_hidden(A_57, C_59))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.34  tff(c_34, plain, (k2_zfmisc_1('#skF_5', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.43/1.34  tff(c_184, plain, (![A_38, C_39, B_40, D_41]: (r2_hidden(A_38, C_39) | ~r2_hidden(k4_tarski(A_38, B_40), k2_zfmisc_1(C_39, D_41)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.34  tff(c_187, plain, (![A_38, B_40]: (r2_hidden(A_38, '#skF_5') | ~r2_hidden(k4_tarski(A_38, B_40), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_184])).
% 2.43/1.34  tff(c_245, plain, (![A_57, B_58]: (r2_hidden(A_57, '#skF_5') | ~r2_hidden(B_58, '#skF_5') | ~r2_hidden(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_225, c_187])).
% 2.43/1.34  tff(c_252, plain, (![B_61]: (~r2_hidden(B_61, '#skF_5'))), inference(splitLeft, [status(thm)], [c_245])).
% 2.43/1.34  tff(c_275, plain, (![B_62]: (r1_tarski('#skF_5', B_62))), inference(resolution, [status(thm)], [c_8, c_252])).
% 2.43/1.34  tff(c_18, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.34  tff(c_280, plain, (![B_63]: (k3_xboole_0('#skF_5', B_63)='#skF_5')), inference(resolution, [status(thm)], [c_275, c_18])).
% 2.43/1.34  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.43/1.34  tff(c_73, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.34  tff(c_78, plain, (![A_23]: (k3_xboole_0(k1_xboole_0, A_23)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_73])).
% 2.43/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.43/1.34  tff(c_83, plain, (![A_23]: (k3_xboole_0(A_23, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78, c_2])).
% 2.43/1.34  tff(c_289, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_280, c_83])).
% 2.43/1.34  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_289])).
% 2.43/1.34  tff(c_318, plain, (![A_64]: (r2_hidden(A_64, '#skF_5') | ~r2_hidden(A_64, '#skF_4'))), inference(splitRight, [status(thm)], [c_245])).
% 2.43/1.34  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.43/1.34  tff(c_336, plain, (![A_65]: (r1_tarski(A_65, '#skF_5') | ~r2_hidden('#skF_1'(A_65, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_318, c_6])).
% 2.43/1.34  tff(c_346, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_336])).
% 2.43/1.34  tff(c_350, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_346, c_18])).
% 2.43/1.34  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.43/1.34  tff(c_180, plain, (![B_34, D_35, A_36, C_37]: (r2_hidden(B_34, D_35) | ~r2_hidden(k4_tarski(A_36, B_34), k2_zfmisc_1(C_37, D_35)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.34  tff(c_183, plain, (![B_34, A_36]: (r2_hidden(B_34, '#skF_4') | ~r2_hidden(k4_tarski(A_36, B_34), k2_zfmisc_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_180])).
% 2.43/1.34  tff(c_246, plain, (![B_58, A_57]: (r2_hidden(B_58, '#skF_4') | ~r2_hidden(B_58, '#skF_5') | ~r2_hidden(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_225, c_183])).
% 2.43/1.34  tff(c_395, plain, (![A_70]: (~r2_hidden(A_70, '#skF_4'))), inference(splitLeft, [status(thm)], [c_246])).
% 2.43/1.34  tff(c_419, plain, (![B_71]: (r1_tarski('#skF_4', B_71))), inference(resolution, [status(thm)], [c_8, c_395])).
% 2.43/1.34  tff(c_431, plain, (![B_72]: (k3_xboole_0('#skF_4', B_72)='#skF_4')), inference(resolution, [status(thm)], [c_419, c_18])).
% 2.43/1.34  tff(c_440, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_431, c_83])).
% 2.43/1.34  tff(c_467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_440])).
% 2.43/1.34  tff(c_469, plain, (![B_73]: (r2_hidden(B_73, '#skF_4') | ~r2_hidden(B_73, '#skF_5'))), inference(splitRight, [status(thm)], [c_246])).
% 2.43/1.34  tff(c_496, plain, (![B_74]: (r2_hidden('#skF_1'('#skF_5', B_74), '#skF_4') | r1_tarski('#skF_5', B_74))), inference(resolution, [status(thm)], [c_8, c_469])).
% 2.43/1.34  tff(c_510, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_496, c_6])).
% 2.43/1.34  tff(c_542, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_510, c_18])).
% 2.43/1.34  tff(c_546, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_542, c_2])).
% 2.43/1.34  tff(c_558, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_546])).
% 2.43/1.34  tff(c_560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_558])).
% 2.43/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.34  
% 2.43/1.34  Inference rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Ref     : 0
% 2.43/1.34  #Sup     : 118
% 2.43/1.34  #Fact    : 0
% 2.43/1.34  #Define  : 0
% 2.43/1.34  #Split   : 2
% 2.43/1.34  #Chain   : 0
% 2.43/1.34  #Close   : 0
% 2.43/1.34  
% 2.43/1.34  Ordering : KBO
% 2.43/1.34  
% 2.43/1.34  Simplification rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Subsume      : 8
% 2.43/1.34  #Demod        : 15
% 2.43/1.34  #Tautology    : 51
% 2.43/1.34  #SimpNegUnit  : 5
% 2.43/1.34  #BackRed      : 2
% 2.43/1.34  
% 2.43/1.34  #Partial instantiations: 0
% 2.43/1.34  #Strategies tried      : 1
% 2.43/1.34  
% 2.43/1.34  Timing (in seconds)
% 2.43/1.34  ----------------------
% 2.43/1.34  Preprocessing        : 0.29
% 2.43/1.34  Parsing              : 0.15
% 2.43/1.34  CNF conversion       : 0.02
% 2.43/1.34  Main loop            : 0.28
% 2.43/1.34  Inferencing          : 0.11
% 2.43/1.34  Reduction            : 0.07
% 2.43/1.34  Demodulation         : 0.05
% 2.43/1.34  BG Simplification    : 0.02
% 2.43/1.34  Subsumption          : 0.06
% 2.43/1.34  Abstraction          : 0.01
% 2.43/1.34  MUC search           : 0.00
% 2.43/1.34  Cooper               : 0.00
% 2.43/1.34  Total                : 0.59
% 2.43/1.34  Index Insertion      : 0.00
% 2.43/1.34  Index Deletion       : 0.00
% 2.43/1.34  Index Matching       : 0.00
% 2.43/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
