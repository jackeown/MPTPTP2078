%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:49 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   46 (  66 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 111 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_56,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_55,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
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

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_51,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_51])).

tff(c_36,plain,(
    ! [A_22] : v1_funct_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_232,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_4'(A_60,B_61),k1_relat_1(B_61))
      | v5_funct_1(B_61,A_60)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_235,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_4'(A_60,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_60)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_232])).

tff(c_237,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_4'(A_60,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_60)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_46,c_235])).

tff(c_266,plain,(
    ! [A_66] :
      ( r2_hidden('#skF_4'(A_66,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_46,c_235])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,B_34)
      | ~ r2_hidden(C_35,A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [C_35,A_6] :
      ( ~ r2_hidden(C_35,k1_xboole_0)
      | ~ r2_hidden(C_35,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_364,plain,(
    ! [A_79,A_80] :
      ( ~ r2_hidden('#skF_4'(A_79,k1_xboole_0),A_80)
      | v5_funct_1(k1_xboole_0,A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_266,c_84])).

tff(c_380,plain,(
    ! [A_81] :
      ( v5_funct_1(k1_xboole_0,A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_237,c_364])).

tff(c_38,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_383,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_380,c_38])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.31  
% 2.42/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.32  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.42/1.32  
% 2.42/1.32  %Foreground sorts:
% 2.42/1.32  
% 2.42/1.32  
% 2.42/1.32  %Background operators:
% 2.42/1.32  
% 2.42/1.32  
% 2.42/1.32  %Foreground operators:
% 2.42/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.42/1.32  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.42/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.42/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.42/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.42/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.42/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.42/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.42/1.32  
% 2.42/1.33  tff(f_83, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.42/1.33  tff(f_56, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.42/1.33  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.42/1.33  tff(f_55, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.42/1.33  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.42/1.33  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.42/1.33  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.42/1.33  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.42/1.33  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.42/1.33  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.42/1.33  tff(c_51, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.42/1.33  tff(c_53, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_51])).
% 2.42/1.33  tff(c_36, plain, (![A_22]: (v1_funct_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.42/1.33  tff(c_46, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_36])).
% 2.42/1.33  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.42/1.33  tff(c_232, plain, (![A_60, B_61]: (r2_hidden('#skF_4'(A_60, B_61), k1_relat_1(B_61)) | v5_funct_1(B_61, A_60) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.42/1.33  tff(c_235, plain, (![A_60]: (r2_hidden('#skF_4'(A_60, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_60) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(superposition, [status(thm), theory('equality')], [c_24, c_232])).
% 2.42/1.33  tff(c_237, plain, (![A_60]: (r2_hidden('#skF_4'(A_60, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_60) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_46, c_235])).
% 2.42/1.33  tff(c_266, plain, (![A_66]: (r2_hidden('#skF_4'(A_66, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_46, c_235])).
% 2.42/1.33  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.42/1.33  tff(c_81, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, B_34) | ~r2_hidden(C_35, A_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.42/1.33  tff(c_84, plain, (![C_35, A_6]: (~r2_hidden(C_35, k1_xboole_0) | ~r2_hidden(C_35, A_6))), inference(resolution, [status(thm)], [c_8, c_81])).
% 2.42/1.33  tff(c_364, plain, (![A_79, A_80]: (~r2_hidden('#skF_4'(A_79, k1_xboole_0), A_80) | v5_funct_1(k1_xboole_0, A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_266, c_84])).
% 2.42/1.33  tff(c_380, plain, (![A_81]: (v5_funct_1(k1_xboole_0, A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_237, c_364])).
% 2.42/1.33  tff(c_38, plain, (~v5_funct_1(k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.42/1.33  tff(c_383, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_380, c_38])).
% 2.42/1.33  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_383])).
% 2.42/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.33  
% 2.42/1.33  Inference rules
% 2.42/1.33  ----------------------
% 2.42/1.33  #Ref     : 0
% 2.42/1.33  #Sup     : 78
% 2.42/1.33  #Fact    : 0
% 2.42/1.33  #Define  : 0
% 2.42/1.33  #Split   : 0
% 2.42/1.33  #Chain   : 0
% 2.42/1.33  #Close   : 0
% 2.42/1.33  
% 2.42/1.33  Ordering : KBO
% 2.42/1.33  
% 2.42/1.33  Simplification rules
% 2.42/1.33  ----------------------
% 2.42/1.33  #Subsume      : 7
% 2.42/1.33  #Demod        : 25
% 2.42/1.33  #Tautology    : 35
% 2.42/1.33  #SimpNegUnit  : 0
% 2.42/1.33  #BackRed      : 0
% 2.42/1.33  
% 2.42/1.33  #Partial instantiations: 0
% 2.42/1.33  #Strategies tried      : 1
% 2.42/1.33  
% 2.42/1.33  Timing (in seconds)
% 2.42/1.33  ----------------------
% 2.42/1.33  Preprocessing        : 0.30
% 2.42/1.33  Parsing              : 0.16
% 2.42/1.33  CNF conversion       : 0.02
% 2.42/1.33  Main loop            : 0.27
% 2.42/1.33  Inferencing          : 0.11
% 2.42/1.33  Reduction            : 0.07
% 2.42/1.33  Demodulation         : 0.05
% 2.42/1.33  BG Simplification    : 0.02
% 2.42/1.33  Subsumption          : 0.05
% 2.42/1.33  Abstraction          : 0.01
% 2.42/1.33  MUC search           : 0.00
% 2.42/1.33  Cooper               : 0.00
% 2.42/1.33  Total                : 0.60
% 2.42/1.33  Index Insertion      : 0.00
% 2.42/1.33  Index Deletion       : 0.00
% 2.42/1.33  Index Matching       : 0.00
% 2.42/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
