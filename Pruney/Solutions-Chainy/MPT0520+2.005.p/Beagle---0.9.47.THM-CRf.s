%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:08 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   57 (  64 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   65 (  84 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k2_relat_1(B))
         => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_73,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_44,plain,(
    k2_relat_1(k8_relat_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_182,plain,(
    ! [D_51,B_52,A_53] :
      ( ~ r2_hidden(D_51,B_52)
      | ~ r2_hidden(D_51,k4_xboole_0(A_53,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2197,plain,(
    ! [A_192,A_193,B_194] :
      ( ~ r2_hidden('#skF_3'(A_192,k4_xboole_0(A_193,B_194)),B_194)
      | r1_xboole_0(A_192,k4_xboole_0(A_193,B_194)) ) ),
    inference(resolution,[status(thm)],[c_22,c_182])).

tff(c_2253,plain,(
    ! [A_197,A_198] : r1_xboole_0(A_197,k4_xboole_0(A_198,A_197)) ),
    inference(resolution,[status(thm)],[c_24,c_2197])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2659,plain,(
    ! [A_204,A_205] : k4_xboole_0(A_204,k4_xboole_0(A_205,A_204)) = A_204 ),
    inference(resolution,[status(thm)],[c_2253,c_30])).

tff(c_46,plain,(
    r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_261,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_xboole_0(A_68,C_69)
      | ~ r1_xboole_0(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_367,plain,(
    ! [A_84,B_85,A_86] :
      ( r1_xboole_0(A_84,B_85)
      | ~ r1_tarski(A_84,A_86)
      | k4_xboole_0(A_86,B_85) != A_86 ) ),
    inference(resolution,[status(thm)],[c_32,c_261])).

tff(c_370,plain,(
    ! [B_85] :
      ( r1_xboole_0('#skF_4',B_85)
      | k4_xboole_0(k2_relat_1('#skF_5'),B_85) != k2_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_367])).

tff(c_2915,plain,(
    ! [A_206] : r1_xboole_0('#skF_4',k4_xboole_0(A_206,k2_relat_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2659,c_370])).

tff(c_3169,plain,(
    ! [A_218] : k4_xboole_0('#skF_4',k4_xboole_0(A_218,k2_relat_1('#skF_5'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2915,c_30])).

tff(c_26,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3294,plain,(
    k3_xboole_0('#skF_4',k2_relat_1('#skF_5')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3169,c_26])).

tff(c_265,plain,(
    ! [B_71,A_72] :
      ( k3_xboole_0(k2_relat_1(B_71),A_72) = k2_relat_1(k8_relat_1(A_72,B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_83,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_112,plain,(
    ! [B_40,A_41] : k1_setfam_1(k2_tarski(B_40,A_41)) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_83])).

tff(c_40,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_118,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_40])).

tff(c_277,plain,(
    ! [A_72,B_71] :
      ( k3_xboole_0(A_72,k2_relat_1(B_71)) = k2_relat_1(k8_relat_1(A_72,B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_118])).

tff(c_3393,plain,
    ( k2_relat_1(k8_relat_1('#skF_4','#skF_5')) = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3294,c_277])).

tff(c_3413,plain,(
    k2_relat_1(k8_relat_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3393])).

tff(c_3415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_3413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.94  
% 4.81/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 4.81/1.94  
% 4.81/1.94  %Foreground sorts:
% 4.81/1.94  
% 4.81/1.94  
% 4.81/1.94  %Background operators:
% 4.81/1.94  
% 4.81/1.94  
% 4.81/1.94  %Foreground operators:
% 4.81/1.94  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.81/1.94  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.81/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.81/1.94  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.81/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.81/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.81/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.81/1.94  tff('#skF_5', type, '#skF_5': $i).
% 4.81/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.81/1.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.81/1.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.81/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.81/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.81/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.81/1.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.81/1.94  
% 4.81/1.96  tff(f_84, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_relat_1)).
% 4.81/1.96  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.81/1.96  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.81/1.96  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.81/1.96  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.81/1.96  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.81/1.96  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 4.81/1.96  tff(f_67, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.81/1.96  tff(f_73, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.81/1.96  tff(c_44, plain, (k2_relat_1(k8_relat_1('#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.81/1.96  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.81/1.96  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.81/1.96  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.81/1.96  tff(c_182, plain, (![D_51, B_52, A_53]: (~r2_hidden(D_51, B_52) | ~r2_hidden(D_51, k4_xboole_0(A_53, B_52)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.81/1.96  tff(c_2197, plain, (![A_192, A_193, B_194]: (~r2_hidden('#skF_3'(A_192, k4_xboole_0(A_193, B_194)), B_194) | r1_xboole_0(A_192, k4_xboole_0(A_193, B_194)))), inference(resolution, [status(thm)], [c_22, c_182])).
% 4.81/1.96  tff(c_2253, plain, (![A_197, A_198]: (r1_xboole_0(A_197, k4_xboole_0(A_198, A_197)))), inference(resolution, [status(thm)], [c_24, c_2197])).
% 4.81/1.96  tff(c_30, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/1.96  tff(c_2659, plain, (![A_204, A_205]: (k4_xboole_0(A_204, k4_xboole_0(A_205, A_204))=A_204)), inference(resolution, [status(thm)], [c_2253, c_30])).
% 4.81/1.96  tff(c_46, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.81/1.96  tff(c_32, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/1.96  tff(c_261, plain, (![A_68, C_69, B_70]: (r1_xboole_0(A_68, C_69) | ~r1_xboole_0(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.81/1.96  tff(c_367, plain, (![A_84, B_85, A_86]: (r1_xboole_0(A_84, B_85) | ~r1_tarski(A_84, A_86) | k4_xboole_0(A_86, B_85)!=A_86)), inference(resolution, [status(thm)], [c_32, c_261])).
% 4.81/1.96  tff(c_370, plain, (![B_85]: (r1_xboole_0('#skF_4', B_85) | k4_xboole_0(k2_relat_1('#skF_5'), B_85)!=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_367])).
% 4.81/1.96  tff(c_2915, plain, (![A_206]: (r1_xboole_0('#skF_4', k4_xboole_0(A_206, k2_relat_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_2659, c_370])).
% 4.81/1.96  tff(c_3169, plain, (![A_218]: (k4_xboole_0('#skF_4', k4_xboole_0(A_218, k2_relat_1('#skF_5')))='#skF_4')), inference(resolution, [status(thm)], [c_2915, c_30])).
% 4.81/1.96  tff(c_26, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.81/1.96  tff(c_3294, plain, (k3_xboole_0('#skF_4', k2_relat_1('#skF_5'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3169, c_26])).
% 4.81/1.96  tff(c_265, plain, (![B_71, A_72]: (k3_xboole_0(k2_relat_1(B_71), A_72)=k2_relat_1(k8_relat_1(A_72, B_71)) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.81/1.96  tff(c_34, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.81/1.96  tff(c_83, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.81/1.96  tff(c_112, plain, (![B_40, A_41]: (k1_setfam_1(k2_tarski(B_40, A_41))=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_34, c_83])).
% 4.81/1.96  tff(c_40, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.81/1.96  tff(c_118, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_112, c_40])).
% 4.81/1.96  tff(c_277, plain, (![A_72, B_71]: (k3_xboole_0(A_72, k2_relat_1(B_71))=k2_relat_1(k8_relat_1(A_72, B_71)) | ~v1_relat_1(B_71))), inference(superposition, [status(thm), theory('equality')], [c_265, c_118])).
% 4.81/1.96  tff(c_3393, plain, (k2_relat_1(k8_relat_1('#skF_4', '#skF_5'))='#skF_4' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3294, c_277])).
% 4.81/1.96  tff(c_3413, plain, (k2_relat_1(k8_relat_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3393])).
% 4.81/1.96  tff(c_3415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_3413])).
% 4.81/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.96  
% 4.81/1.96  Inference rules
% 4.81/1.96  ----------------------
% 4.81/1.96  #Ref     : 0
% 4.81/1.96  #Sup     : 872
% 4.81/1.96  #Fact    : 0
% 4.81/1.96  #Define  : 0
% 4.81/1.96  #Split   : 1
% 4.81/1.96  #Chain   : 0
% 4.81/1.96  #Close   : 0
% 4.81/1.96  
% 4.81/1.96  Ordering : KBO
% 4.81/1.96  
% 4.81/1.96  Simplification rules
% 4.81/1.96  ----------------------
% 4.81/1.96  #Subsume      : 33
% 4.81/1.96  #Demod        : 291
% 4.81/1.96  #Tautology    : 258
% 4.81/1.96  #SimpNegUnit  : 1
% 4.81/1.96  #BackRed      : 0
% 4.81/1.96  
% 4.81/1.96  #Partial instantiations: 0
% 4.81/1.96  #Strategies tried      : 1
% 4.81/1.96  
% 4.81/1.96  Timing (in seconds)
% 4.81/1.96  ----------------------
% 4.81/1.96  Preprocessing        : 0.33
% 4.81/1.96  Parsing              : 0.17
% 4.81/1.96  CNF conversion       : 0.02
% 4.81/1.96  Main loop            : 0.87
% 4.81/1.96  Inferencing          : 0.26
% 4.81/1.96  Reduction            : 0.33
% 4.81/1.96  Demodulation         : 0.27
% 4.81/1.96  BG Simplification    : 0.04
% 4.81/1.96  Subsumption          : 0.18
% 4.81/1.96  Abstraction          : 0.04
% 4.81/1.96  MUC search           : 0.00
% 4.81/1.96  Cooper               : 0.00
% 4.81/1.96  Total                : 1.23
% 4.81/1.96  Index Insertion      : 0.00
% 4.81/1.96  Index Deletion       : 0.00
% 4.81/1.96  Index Matching       : 0.00
% 4.81/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
