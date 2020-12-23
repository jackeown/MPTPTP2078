%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:45 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 109 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_32,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_72,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_195,plain,(
    ! [B_46,A_47] :
      ( k3_xboole_0(k1_relat_1(B_46),A_47) = k1_relat_1(k7_relat_1(B_46,A_47))
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_122,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_38])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_132,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_141,plain,(
    ! [A_39,B_40] :
      ( ~ r1_xboole_0(A_39,B_40)
      | k3_xboole_0(A_39,B_40) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_148,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_141])).

tff(c_204,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_148])).

tff(c_235,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_204])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k7_relat_1(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_112,plain,(
    ! [A_33] :
      ( k1_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_264,plain,(
    ! [A_50,B_51] :
      ( k1_relat_1(k7_relat_1(A_50,B_51)) != k1_xboole_0
      | k7_relat_1(A_50,B_51) = k1_xboole_0
      | ~ v1_relat_1(A_50) ) ),
    inference(resolution,[status(thm)],[c_18,c_112])).

tff(c_270,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_264])).

tff(c_274,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_270])).

tff(c_276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_274])).

tff(c_277,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,B_27)
      | ~ r1_xboole_0(k1_tarski(A_26),B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_278,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_407,plain,(
    ! [B_69,A_70] :
      ( k3_xboole_0(k1_relat_1(B_69),A_70) = k1_relat_1(k7_relat_1(B_69,A_70))
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_794,plain,(
    ! [B_89,A_90] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_89),A_90),k1_relat_1(k7_relat_1(B_89,A_90)))
      | r1_xboole_0(k1_relat_1(B_89),A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_2])).

tff(c_830,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_4'),'#skF_3'),k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_794])).

tff(c_852,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_4'),'#skF_3'),k1_xboole_0)
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22,c_830])).

tff(c_854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_64,c_852])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.37  
% 2.54/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.37  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.54/1.37  
% 2.54/1.37  %Foreground sorts:
% 2.54/1.37  
% 2.54/1.37  
% 2.54/1.37  %Background operators:
% 2.54/1.37  
% 2.54/1.37  
% 2.54/1.37  %Foreground operators:
% 2.54/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.54/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.54/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.54/1.37  
% 2.54/1.38  tff(f_86, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.54/1.38  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.54/1.38  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.54/1.38  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.54/1.38  tff(f_64, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.54/1.38  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.54/1.38  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.54/1.38  tff(f_58, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.54/1.38  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.54/1.38  tff(c_32, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.54/1.38  tff(c_72, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.54/1.38  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.54/1.38  tff(c_195, plain, (![B_46, A_47]: (k3_xboole_0(k1_relat_1(B_46), A_47)=k1_relat_1(k7_relat_1(B_46, A_47)) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.54/1.38  tff(c_38, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.54/1.38  tff(c_122, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_38])).
% 2.54/1.38  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.54/1.38  tff(c_132, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.38  tff(c_141, plain, (![A_39, B_40]: (~r1_xboole_0(A_39, B_40) | k3_xboole_0(A_39, B_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_132])).
% 2.54/1.38  tff(c_148, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_141])).
% 2.54/1.38  tff(c_204, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_195, c_148])).
% 2.54/1.38  tff(c_235, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_204])).
% 2.54/1.38  tff(c_18, plain, (![A_16, B_17]: (v1_relat_1(k7_relat_1(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.54/1.38  tff(c_112, plain, (![A_33]: (k1_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.54/1.38  tff(c_264, plain, (![A_50, B_51]: (k1_relat_1(k7_relat_1(A_50, B_51))!=k1_xboole_0 | k7_relat_1(A_50, B_51)=k1_xboole_0 | ~v1_relat_1(A_50))), inference(resolution, [status(thm)], [c_18, c_112])).
% 2.54/1.38  tff(c_270, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_235, c_264])).
% 2.54/1.38  tff(c_274, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_270])).
% 2.54/1.38  tff(c_276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_274])).
% 2.54/1.38  tff(c_277, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.54/1.38  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.38  tff(c_59, plain, (![A_26, B_27]: (~r2_hidden(A_26, B_27) | ~r1_xboole_0(k1_tarski(A_26), B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.54/1.38  tff(c_64, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_59])).
% 2.54/1.38  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.54/1.38  tff(c_278, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.54/1.38  tff(c_407, plain, (![B_69, A_70]: (k3_xboole_0(k1_relat_1(B_69), A_70)=k1_relat_1(k7_relat_1(B_69, A_70)) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.54/1.38  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.38  tff(c_794, plain, (![B_89, A_90]: (r2_hidden('#skF_1'(k1_relat_1(B_89), A_90), k1_relat_1(k7_relat_1(B_89, A_90))) | r1_xboole_0(k1_relat_1(B_89), A_90) | ~v1_relat_1(B_89))), inference(superposition, [status(thm), theory('equality')], [c_407, c_2])).
% 2.54/1.38  tff(c_830, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4'), '#skF_3'), k1_relat_1(k1_xboole_0)) | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_278, c_794])).
% 2.54/1.38  tff(c_852, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4'), '#skF_3'), k1_xboole_0) | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22, c_830])).
% 2.54/1.38  tff(c_854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277, c_64, c_852])).
% 2.54/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.38  
% 2.54/1.38  Inference rules
% 2.54/1.38  ----------------------
% 2.54/1.38  #Ref     : 0
% 2.54/1.38  #Sup     : 187
% 2.54/1.38  #Fact    : 0
% 2.54/1.38  #Define  : 0
% 2.54/1.38  #Split   : 6
% 2.54/1.38  #Chain   : 0
% 2.54/1.38  #Close   : 0
% 2.54/1.38  
% 2.54/1.38  Ordering : KBO
% 2.54/1.38  
% 2.54/1.38  Simplification rules
% 2.54/1.38  ----------------------
% 2.54/1.38  #Subsume      : 27
% 2.54/1.38  #Demod        : 132
% 2.54/1.38  #Tautology    : 99
% 2.54/1.38  #SimpNegUnit  : 12
% 2.54/1.38  #BackRed      : 0
% 2.54/1.38  
% 2.54/1.38  #Partial instantiations: 0
% 2.54/1.38  #Strategies tried      : 1
% 2.54/1.38  
% 2.54/1.38  Timing (in seconds)
% 2.54/1.38  ----------------------
% 2.54/1.38  Preprocessing        : 0.31
% 2.54/1.38  Parsing              : 0.16
% 2.54/1.38  CNF conversion       : 0.02
% 2.54/1.38  Main loop            : 0.32
% 2.54/1.38  Inferencing          : 0.13
% 2.54/1.38  Reduction            : 0.10
% 2.54/1.38  Demodulation         : 0.07
% 2.54/1.38  BG Simplification    : 0.02
% 2.54/1.39  Subsumption          : 0.05
% 2.54/1.39  Abstraction          : 0.02
% 2.54/1.39  MUC search           : 0.00
% 2.54/1.39  Cooper               : 0.00
% 2.54/1.39  Total                : 0.65
% 2.54/1.39  Index Insertion      : 0.00
% 2.54/1.39  Index Deletion       : 0.00
% 2.54/1.39  Index Matching       : 0.00
% 2.54/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
