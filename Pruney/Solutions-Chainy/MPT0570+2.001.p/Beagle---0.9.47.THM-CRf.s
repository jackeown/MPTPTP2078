%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:41 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 117 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 170 expanded)
%              Number of equality atoms :   27 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_66,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( r1_xboole_0(k2_relat_1(B_22),A_21)
      | k10_relat_1(B_22,A_21) != k1_xboole_0
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_115,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_115])).

tff(c_196,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_211,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_196])).

tff(c_217,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_211])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_352,plain,(
    ! [A_57,B_58] :
      ( ~ r1_xboole_0(A_57,B_58)
      | v1_xboole_0(k3_xboole_0(A_57,B_58)) ) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_363,plain,
    ( ~ r1_xboole_0('#skF_3',k2_relat_1('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_352])).

tff(c_374,plain,(
    ~ r1_xboole_0('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_363])).

tff(c_328,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),k3_xboole_0(A_55,B_56))
      | r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_376,plain,(
    ! [A_59,B_60] :
      ( ~ v1_xboole_0(k3_xboole_0(A_59,B_60))
      | r1_xboole_0(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_328,c_2])).

tff(c_385,plain,
    ( ~ v1_xboole_0('#skF_3')
    | r1_xboole_0('#skF_3',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_376])).

tff(c_395,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_385])).

tff(c_22,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_100,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_134,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(B_42,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_100])).

tff(c_24,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_140,plain,(
    ! [B_42,A_41] : k3_xboole_0(B_42,A_41) = k3_xboole_0(A_41,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_24])).

tff(c_439,plain,(
    ! [A_69,B_70] :
      ( ~ r1_xboole_0(A_69,B_70)
      | v1_xboole_0(k3_xboole_0(B_70,A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_352])).

tff(c_456,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_439])).

tff(c_469,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_395,c_456])).

tff(c_472,plain,
    ( k10_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_469])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_472])).

tff(c_477,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [B_27,A_28] :
      ( ~ v1_xboole_0(B_27)
      | B_27 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_59,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_481,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_477,c_59])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 20:33:53 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.98  
% 2.85/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.99  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.85/1.99  
% 2.85/1.99  %Foreground sorts:
% 2.85/1.99  
% 2.85/1.99  
% 2.85/1.99  %Background operators:
% 2.85/1.99  
% 2.85/1.99  
% 2.85/1.99  %Foreground operators:
% 2.85/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.85/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.85/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.85/1.99  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.99  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.85/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.99  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.85/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.85/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.99  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.85/1.99  
% 2.85/2.02  tff(f_83, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.85/2.02  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.85/2.02  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.85/2.02  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.85/2.02  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.85/2.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.85/2.02  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.85/2.02  tff(f_64, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.85/2.02  tff(f_66, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.85/2.02  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.85/2.02  tff(f_62, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.85/2.02  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.85/2.02  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.85/2.02  tff(c_30, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.85/2.02  tff(c_28, plain, (![B_22, A_21]: (r1_xboole_0(k2_relat_1(B_22), A_21) | k10_relat_1(B_22, A_21)!=k1_xboole_0 | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.85/2.02  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.85/2.02  tff(c_32, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.85/2.02  tff(c_115, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.85/2.02  tff(c_123, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_115])).
% 2.85/2.02  tff(c_196, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.85/2.02  tff(c_211, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_123, c_196])).
% 2.85/2.02  tff(c_217, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_211])).
% 2.85/2.02  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/2.02  tff(c_128, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.85/2.02  tff(c_352, plain, (![A_57, B_58]: (~r1_xboole_0(A_57, B_58) | v1_xboole_0(k3_xboole_0(A_57, B_58)))), inference(resolution, [status(thm)], [c_4, c_128])).
% 2.85/2.02  tff(c_363, plain, (~r1_xboole_0('#skF_3', k2_relat_1('#skF_4')) | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_217, c_352])).
% 2.85/2.02  tff(c_374, plain, (~r1_xboole_0('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_363])).
% 2.85/2.02  tff(c_328, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), k3_xboole_0(A_55, B_56)) | r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.85/2.02  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/2.02  tff(c_376, plain, (![A_59, B_60]: (~v1_xboole_0(k3_xboole_0(A_59, B_60)) | r1_xboole_0(A_59, B_60))), inference(resolution, [status(thm)], [c_328, c_2])).
% 2.85/2.02  tff(c_385, plain, (~v1_xboole_0('#skF_3') | r1_xboole_0('#skF_3', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_217, c_376])).
% 2.85/2.02  tff(c_395, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_374, c_385])).
% 2.85/2.02  tff(c_22, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.85/2.02  tff(c_100, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.85/2.02  tff(c_134, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(B_42, A_41))), inference(superposition, [status(thm), theory('equality')], [c_22, c_100])).
% 2.85/2.02  tff(c_24, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.85/2.02  tff(c_140, plain, (![B_42, A_41]: (k3_xboole_0(B_42, A_41)=k3_xboole_0(A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_134, c_24])).
% 2.85/2.02  tff(c_439, plain, (![A_69, B_70]: (~r1_xboole_0(A_69, B_70) | v1_xboole_0(k3_xboole_0(B_70, A_69)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_352])).
% 2.85/2.02  tff(c_456, plain, (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_217, c_439])).
% 2.85/2.02  tff(c_469, plain, (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_395, c_456])).
% 2.85/2.02  tff(c_472, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_469])).
% 2.85/2.02  tff(c_476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_472])).
% 2.85/2.02  tff(c_477, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_363])).
% 2.85/2.02  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.85/2.02  tff(c_56, plain, (![B_27, A_28]: (~v1_xboole_0(B_27) | B_27=A_28 | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.85/2.02  tff(c_59, plain, (![A_28]: (k1_xboole_0=A_28 | ~v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_6, c_56])).
% 2.85/2.02  tff(c_481, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_477, c_59])).
% 2.85/2.02  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_481])).
% 2.85/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/2.02  
% 2.85/2.02  Inference rules
% 2.85/2.02  ----------------------
% 2.85/2.02  #Ref     : 0
% 2.85/2.02  #Sup     : 113
% 2.85/2.02  #Fact    : 0
% 2.85/2.02  #Define  : 0
% 2.85/2.02  #Split   : 5
% 2.85/2.02  #Chain   : 0
% 2.85/2.02  #Close   : 0
% 2.85/2.02  
% 2.85/2.02  Ordering : KBO
% 2.85/2.02  
% 2.85/2.02  Simplification rules
% 2.85/2.02  ----------------------
% 2.85/2.02  #Subsume      : 12
% 2.85/2.02  #Demod        : 21
% 2.85/2.02  #Tautology    : 54
% 2.85/2.02  #SimpNegUnit  : 6
% 2.85/2.02  #BackRed      : 0
% 2.85/2.02  
% 2.85/2.02  #Partial instantiations: 0
% 2.85/2.02  #Strategies tried      : 1
% 2.85/2.02  
% 2.85/2.02  Timing (in seconds)
% 2.85/2.02  ----------------------
% 2.85/2.02  Preprocessing        : 0.54
% 2.85/2.02  Parsing              : 0.30
% 2.85/2.02  CNF conversion       : 0.04
% 2.85/2.02  Main loop            : 0.51
% 2.85/2.02  Inferencing          : 0.20
% 2.85/2.02  Reduction            : 0.15
% 2.85/2.02  Demodulation         : 0.11
% 2.85/2.02  BG Simplification    : 0.02
% 2.85/2.02  Subsumption          : 0.10
% 2.85/2.02  Abstraction          : 0.02
% 2.85/2.03  MUC search           : 0.00
% 2.85/2.03  Cooper               : 0.00
% 2.85/2.03  Total                : 1.11
% 2.85/2.03  Index Insertion      : 0.00
% 2.85/2.03  Index Deletion       : 0.00
% 2.85/2.03  Index Matching       : 0.00
% 2.85/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
