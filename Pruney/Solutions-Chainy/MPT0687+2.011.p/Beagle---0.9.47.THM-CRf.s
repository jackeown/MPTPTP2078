%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:34 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 128 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,
    ( r2_hidden('#skF_4',k2_relat_1('#skF_5'))
    | k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_65,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(k1_tarski(A_13),B_14)
      | r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(C_31,B_30)
      | ~ r2_hidden(C_31,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,k1_tarski(A_50))
      | r2_hidden(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_28,c_67])).

tff(c_224,plain,(
    ! [A_66,B_67,A_68] :
      ( ~ r2_hidden('#skF_1'(A_66,B_67),k1_tarski(A_68))
      | r2_hidden(A_68,A_66)
      | r1_xboole_0(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_251,plain,(
    ! [A_69,A_70] :
      ( r2_hidden(A_69,A_70)
      | r1_xboole_0(A_70,k1_tarski(A_69)) ) ),
    inference(resolution,[status(thm)],[c_4,c_224])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( k10_relat_1(B_16,A_15) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_279,plain,(
    ! [B_77,A_78] :
      ( k10_relat_1(B_77,k1_tarski(A_78)) = k1_xboole_0
      | ~ v1_relat_1(B_77)
      | r2_hidden(A_78,k2_relat_1(B_77)) ) ),
    inference(resolution,[status(thm)],[c_251,c_30])).

tff(c_36,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_294,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_279,c_66])).

tff(c_300,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_294])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_300])).

tff(c_303,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_303])).

tff(c_307,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_306,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    ! [D_18,B_19] : r2_hidden(D_18,k2_tarski(D_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_55,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_52])).

tff(c_366,plain,(
    ! [B_91,A_92] :
      ( r1_xboole_0(k2_relat_1(B_91),A_92)
      | k10_relat_1(B_91,A_92) != k1_xboole_0
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3947,plain,(
    ! [C_2745,A_2746,B_2747] :
      ( ~ r2_hidden(C_2745,A_2746)
      | ~ r2_hidden(C_2745,k2_relat_1(B_2747))
      | k10_relat_1(B_2747,A_2746) != k1_xboole_0
      | ~ v1_relat_1(B_2747) ) ),
    inference(resolution,[status(thm)],[c_366,c_2])).

tff(c_4037,plain,(
    ! [A_2875,B_2876] :
      ( ~ r2_hidden(A_2875,k2_relat_1(B_2876))
      | k10_relat_1(B_2876,k1_tarski(A_2875)) != k1_xboole_0
      | ~ v1_relat_1(B_2876) ) ),
    inference(resolution,[status(thm)],[c_55,c_3947])).

tff(c_4059,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_306,c_4037])).

tff(c_4082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_307,c_4059])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.85  
% 4.64/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.85  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.64/1.85  
% 4.64/1.85  %Foreground sorts:
% 4.64/1.85  
% 4.64/1.85  
% 4.64/1.85  %Background operators:
% 4.64/1.85  
% 4.64/1.85  
% 4.64/1.85  %Foreground operators:
% 4.64/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.64/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.64/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.64/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.64/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.64/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.64/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.64/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.85  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.64/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.64/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.64/1.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.64/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.64/1.85  
% 4.64/1.86  tff(f_73, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 4.64/1.86  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.64/1.86  tff(f_59, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.64/1.86  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 4.64/1.86  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.64/1.86  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.64/1.86  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.64/1.86  tff(c_42, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5')) | k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.64/1.86  tff(c_65, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 4.64/1.86  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.64/1.86  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.64/1.86  tff(c_28, plain, (![A_13, B_14]: (r1_xboole_0(k1_tarski(A_13), B_14) | r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.64/1.86  tff(c_67, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, B_30) | ~r2_hidden(C_31, B_30) | ~r2_hidden(C_31, A_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.64/1.86  tff(c_134, plain, (![C_48, B_49, A_50]: (~r2_hidden(C_48, B_49) | ~r2_hidden(C_48, k1_tarski(A_50)) | r2_hidden(A_50, B_49))), inference(resolution, [status(thm)], [c_28, c_67])).
% 4.64/1.86  tff(c_224, plain, (![A_66, B_67, A_68]: (~r2_hidden('#skF_1'(A_66, B_67), k1_tarski(A_68)) | r2_hidden(A_68, A_66) | r1_xboole_0(A_66, B_67))), inference(resolution, [status(thm)], [c_6, c_134])).
% 4.64/1.86  tff(c_251, plain, (![A_69, A_70]: (r2_hidden(A_69, A_70) | r1_xboole_0(A_70, k1_tarski(A_69)))), inference(resolution, [status(thm)], [c_4, c_224])).
% 4.64/1.86  tff(c_30, plain, (![B_16, A_15]: (k10_relat_1(B_16, A_15)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.64/1.86  tff(c_279, plain, (![B_77, A_78]: (k10_relat_1(B_77, k1_tarski(A_78))=k1_xboole_0 | ~v1_relat_1(B_77) | r2_hidden(A_78, k2_relat_1(B_77)))), inference(resolution, [status(thm)], [c_251, c_30])).
% 4.64/1.86  tff(c_36, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.64/1.86  tff(c_66, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_36])).
% 4.64/1.86  tff(c_294, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_279, c_66])).
% 4.64/1.86  tff(c_300, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_294])).
% 4.64/1.86  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_300])).
% 4.64/1.86  tff(c_303, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 4.64/1.86  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_303])).
% 4.64/1.86  tff(c_307, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 4.64/1.86  tff(c_306, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_42])).
% 4.64/1.86  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.64/1.86  tff(c_52, plain, (![D_18, B_19]: (r2_hidden(D_18, k2_tarski(D_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.64/1.86  tff(c_55, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_52])).
% 4.64/1.86  tff(c_366, plain, (![B_91, A_92]: (r1_xboole_0(k2_relat_1(B_91), A_92) | k10_relat_1(B_91, A_92)!=k1_xboole_0 | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.64/1.86  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.64/1.86  tff(c_3947, plain, (![C_2745, A_2746, B_2747]: (~r2_hidden(C_2745, A_2746) | ~r2_hidden(C_2745, k2_relat_1(B_2747)) | k10_relat_1(B_2747, A_2746)!=k1_xboole_0 | ~v1_relat_1(B_2747))), inference(resolution, [status(thm)], [c_366, c_2])).
% 4.64/1.86  tff(c_4037, plain, (![A_2875, B_2876]: (~r2_hidden(A_2875, k2_relat_1(B_2876)) | k10_relat_1(B_2876, k1_tarski(A_2875))!=k1_xboole_0 | ~v1_relat_1(B_2876))), inference(resolution, [status(thm)], [c_55, c_3947])).
% 4.64/1.86  tff(c_4059, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_306, c_4037])).
% 4.64/1.86  tff(c_4082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_307, c_4059])).
% 4.64/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.86  
% 4.64/1.86  Inference rules
% 4.64/1.86  ----------------------
% 4.64/1.86  #Ref     : 0
% 4.64/1.86  #Sup     : 558
% 4.64/1.86  #Fact    : 4
% 4.64/1.86  #Define  : 0
% 4.64/1.86  #Split   : 3
% 4.64/1.86  #Chain   : 0
% 4.64/1.86  #Close   : 0
% 4.64/1.86  
% 4.64/1.86  Ordering : KBO
% 4.64/1.86  
% 4.64/1.86  Simplification rules
% 4.64/1.86  ----------------------
% 4.64/1.86  #Subsume      : 81
% 4.64/1.86  #Demod        : 72
% 4.64/1.86  #Tautology    : 92
% 4.64/1.86  #SimpNegUnit  : 2
% 4.64/1.86  #BackRed      : 0
% 4.64/1.86  
% 4.64/1.86  #Partial instantiations: 1920
% 4.64/1.86  #Strategies tried      : 1
% 4.64/1.86  
% 4.64/1.86  Timing (in seconds)
% 4.64/1.86  ----------------------
% 4.64/1.87  Preprocessing        : 0.30
% 4.64/1.87  Parsing              : 0.15
% 4.64/1.87  CNF conversion       : 0.02
% 4.64/1.87  Main loop            : 0.82
% 4.64/1.87  Inferencing          : 0.38
% 4.64/1.87  Reduction            : 0.15
% 4.64/1.87  Demodulation         : 0.12
% 4.64/1.87  BG Simplification    : 0.04
% 4.64/1.87  Subsumption          : 0.20
% 4.64/1.87  Abstraction          : 0.04
% 4.64/1.87  MUC search           : 0.00
% 4.64/1.87  Cooper               : 0.00
% 4.64/1.87  Total                : 1.14
% 4.64/1.87  Index Insertion      : 0.00
% 4.64/1.87  Index Deletion       : 0.00
% 4.64/1.87  Index Matching       : 0.00
% 4.64/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
