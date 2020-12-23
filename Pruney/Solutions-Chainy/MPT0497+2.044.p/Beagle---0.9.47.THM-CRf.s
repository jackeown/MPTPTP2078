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
% DateTime   : Thu Dec  3 09:59:45 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 113 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 188 expanded)
%              Number of equality atoms :   28 (  66 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_34,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_65,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_28,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_86,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_28])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_178,plain,(
    ! [B_39,A_40] :
      ( k3_xboole_0(k1_relat_1(B_39),A_40) = k1_relat_1(k7_relat_1(B_39,A_40))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,k3_xboole_0(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [A_35,B_36] :
      ( ~ r1_xboole_0(A_35,B_36)
      | k3_xboole_0(A_35,B_36) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_87])).

tff(c_123,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_116])).

tff(c_184,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_123])).

tff(c_218,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_184])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k3_xboole_0(k1_relat_1(B_17),A_16) = k1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_225,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_4','#skF_3'),A_16)) = k3_xboole_0(k1_xboole_0,A_16)
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_24])).

tff(c_242,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_245,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_242])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_245])).

tff(c_251,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_22,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_254,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != k1_xboole_0
    | k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_251,c_22])).

tff(c_260,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_254])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_260])).

tff(c_264,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_10,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_309,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_318,plain,(
    ! [A_48,C_49] :
      ( ~ r1_xboole_0(A_48,A_48)
      | ~ r2_hidden(C_49,A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_309])).

tff(c_322,plain,(
    ! [C_49] : ~ r2_hidden(C_49,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_318])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_263,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_426,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_1'(A_58,B_59),k3_xboole_0(A_58,B_59))
      | r1_xboole_0(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_864,plain,(
    ! [B_78,A_79] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_78),A_79),k1_relat_1(k7_relat_1(B_78,A_79)))
      | r1_xboole_0(k1_relat_1(B_78),A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_426])).

tff(c_903,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_4'),'#skF_3'),k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_864])).

tff(c_927,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_4'),'#skF_3'),k1_xboole_0)
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18,c_903])).

tff(c_929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_322,c_927])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.36  
% 2.50/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.36  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.50/1.36  
% 2.50/1.36  %Foreground sorts:
% 2.50/1.36  
% 2.50/1.36  
% 2.50/1.36  %Background operators:
% 2.50/1.36  
% 2.50/1.36  
% 2.50/1.36  %Foreground operators:
% 2.50/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.50/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.50/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.50/1.36  
% 2.68/1.37  tff(f_79, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.68/1.37  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.68/1.37  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.68/1.37  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.68/1.37  tff(f_57, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.68/1.37  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.68/1.37  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.68/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.68/1.37  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.68/1.37  tff(c_34, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.37  tff(c_65, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.68/1.37  tff(c_28, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.37  tff(c_86, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_65, c_28])).
% 2.68/1.37  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.37  tff(c_178, plain, (![B_39, A_40]: (k3_xboole_0(k1_relat_1(B_39), A_40)=k1_relat_1(k7_relat_1(B_39, A_40)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.68/1.37  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.68/1.37  tff(c_87, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, k3_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.37  tff(c_116, plain, (![A_35, B_36]: (~r1_xboole_0(A_35, B_36) | k3_xboole_0(A_35, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_87])).
% 2.68/1.37  tff(c_123, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_65, c_116])).
% 2.68/1.37  tff(c_184, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_178, c_123])).
% 2.68/1.37  tff(c_218, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_184])).
% 2.68/1.37  tff(c_14, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.68/1.37  tff(c_24, plain, (![B_17, A_16]: (k3_xboole_0(k1_relat_1(B_17), A_16)=k1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.68/1.37  tff(c_225, plain, (![A_16]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), A_16))=k3_xboole_0(k1_xboole_0, A_16) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_218, c_24])).
% 2.68/1.37  tff(c_242, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_225])).
% 2.68/1.37  tff(c_245, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_242])).
% 2.68/1.37  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_245])).
% 2.68/1.37  tff(c_251, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_225])).
% 2.68/1.37  tff(c_22, plain, (![A_15]: (k1_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.37  tff(c_254, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!=k1_xboole_0 | k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_251, c_22])).
% 2.68/1.37  tff(c_260, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_218, c_254])).
% 2.68/1.37  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_260])).
% 2.68/1.37  tff(c_264, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.68/1.37  tff(c_10, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.68/1.37  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.37  tff(c_309, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.37  tff(c_318, plain, (![A_48, C_49]: (~r1_xboole_0(A_48, A_48) | ~r2_hidden(C_49, A_48))), inference(superposition, [status(thm), theory('equality')], [c_2, c_309])).
% 2.68/1.37  tff(c_322, plain, (![C_49]: (~r2_hidden(C_49, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_318])).
% 2.68/1.37  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.37  tff(c_263, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.68/1.37  tff(c_426, plain, (![A_58, B_59]: (r2_hidden('#skF_1'(A_58, B_59), k3_xboole_0(A_58, B_59)) | r1_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.37  tff(c_864, plain, (![B_78, A_79]: (r2_hidden('#skF_1'(k1_relat_1(B_78), A_79), k1_relat_1(k7_relat_1(B_78, A_79))) | r1_xboole_0(k1_relat_1(B_78), A_79) | ~v1_relat_1(B_78))), inference(superposition, [status(thm), theory('equality')], [c_24, c_426])).
% 2.68/1.37  tff(c_903, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4'), '#skF_3'), k1_relat_1(k1_xboole_0)) | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_263, c_864])).
% 2.68/1.37  tff(c_927, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4'), '#skF_3'), k1_xboole_0) | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_18, c_903])).
% 2.68/1.37  tff(c_929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_264, c_322, c_927])).
% 2.68/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.37  
% 2.68/1.37  Inference rules
% 2.68/1.37  ----------------------
% 2.68/1.37  #Ref     : 0
% 2.68/1.37  #Sup     : 198
% 2.68/1.37  #Fact    : 0
% 2.68/1.37  #Define  : 0
% 2.68/1.37  #Split   : 5
% 2.68/1.37  #Chain   : 0
% 2.68/1.37  #Close   : 0
% 2.68/1.37  
% 2.68/1.37  Ordering : KBO
% 2.68/1.37  
% 2.68/1.37  Simplification rules
% 2.68/1.37  ----------------------
% 2.68/1.37  #Subsume      : 26
% 2.68/1.37  #Demod        : 172
% 2.68/1.37  #Tautology    : 106
% 2.68/1.37  #SimpNegUnit  : 11
% 2.68/1.37  #BackRed      : 0
% 2.68/1.37  
% 2.68/1.38  #Partial instantiations: 0
% 2.68/1.38  #Strategies tried      : 1
% 2.68/1.38  
% 2.68/1.38  Timing (in seconds)
% 2.68/1.38  ----------------------
% 2.68/1.38  Preprocessing        : 0.29
% 2.68/1.38  Parsing              : 0.16
% 2.68/1.38  CNF conversion       : 0.02
% 2.68/1.38  Main loop            : 0.32
% 2.68/1.38  Inferencing          : 0.13
% 2.68/1.38  Reduction            : 0.10
% 2.68/1.38  Demodulation         : 0.07
% 2.68/1.38  BG Simplification    : 0.02
% 2.68/1.38  Subsumption          : 0.06
% 2.68/1.38  Abstraction          : 0.02
% 2.68/1.38  MUC search           : 0.00
% 2.68/1.38  Cooper               : 0.00
% 2.68/1.38  Total                : 0.65
% 2.68/1.38  Index Insertion      : 0.00
% 2.68/1.38  Index Deletion       : 0.00
% 2.68/1.38  Index Matching       : 0.00
% 2.68/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
