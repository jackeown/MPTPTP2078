%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:44 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   60 (  99 expanded)
%              Number of leaves         :   27 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 149 expanded)
%              Number of equality atoms :   26 (  62 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_268,plain,(
    ! [B_58,A_59] :
      ( r1_xboole_0(k2_relat_1(B_58),A_59)
      | k10_relat_1(B_58,A_59) != k1_xboole_0
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,C_17)
      | ~ r1_xboole_0(B_16,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_422,plain,(
    ! [A_71,A_72,B_73] :
      ( r1_xboole_0(A_71,A_72)
      | ~ r1_tarski(A_71,k2_relat_1(B_73))
      | k10_relat_1(B_73,A_72) != k1_xboole_0
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_268,c_22])).

tff(c_427,plain,(
    ! [A_72] :
      ( r1_xboole_0('#skF_3',A_72)
      | k10_relat_1('#skF_4',A_72) != k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_422])).

tff(c_436,plain,(
    ! [A_74] :
      ( r1_xboole_0('#skF_3',A_74)
      | k10_relat_1('#skF_4',A_74) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_427])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,(
    ! [B_9] : k4_xboole_0(B_9,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_63])).

tff(c_97,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115,plain,(
    ! [B_9] : k4_xboole_0(B_9,k1_xboole_0) = k3_xboole_0(B_9,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_97])).

tff(c_122,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_115])).

tff(c_172,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_178,plain,(
    ! [B_9,C_40] :
      ( ~ r1_xboole_0(B_9,B_9)
      | ~ r2_hidden(C_40,B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_172])).

tff(c_447,plain,(
    ! [C_40] :
      ( ~ r2_hidden(C_40,'#skF_3')
      | k10_relat_1('#skF_4','#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_436,c_178])).

tff(c_453,plain,(
    ! [C_40] : ~ r2_hidden(C_40,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_447])).

tff(c_74,plain,(
    k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_112,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_97])).

tff(c_121,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_112])).

tff(c_175,plain,(
    ! [C_40] :
      ( ~ r1_xboole_0('#skF_3',k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_40,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_172])).

tff(c_198,plain,(
    ~ r1_xboole_0('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_215,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),k3_xboole_0(A_51,B_52))
      | r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_221,plain,
    ( r2_hidden('#skF_1'('#skF_3',k2_relat_1('#skF_4')),'#skF_3')
    | r1_xboole_0('#skF_3',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_215])).

tff(c_229,plain,(
    r2_hidden('#skF_1'('#skF_3',k2_relat_1('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_221])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_229])).

tff(c_458,plain,(
    ! [C_75] : ~ r2_hidden(C_75,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_462,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_458])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.36  
% 2.25/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.25/1.37  
% 2.25/1.37  %Foreground sorts:
% 2.25/1.37  
% 2.25/1.37  
% 2.25/1.37  %Background operators:
% 2.25/1.37  
% 2.25/1.37  
% 2.25/1.37  %Foreground operators:
% 2.25/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.25/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.25/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.25/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.25/1.37  
% 2.25/1.38  tff(f_86, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.25/1.38  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.25/1.38  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.25/1.38  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.25/1.38  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.25/1.38  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.25/1.38  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.25/1.38  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.25/1.38  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.25/1.38  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.25/1.38  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.25/1.38  tff(c_30, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.25/1.38  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.25/1.38  tff(c_32, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.25/1.38  tff(c_268, plain, (![B_58, A_59]: (r1_xboole_0(k2_relat_1(B_58), A_59) | k10_relat_1(B_58, A_59)!=k1_xboole_0 | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.25/1.38  tff(c_22, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, C_17) | ~r1_xboole_0(B_16, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.25/1.38  tff(c_422, plain, (![A_71, A_72, B_73]: (r1_xboole_0(A_71, A_72) | ~r1_tarski(A_71, k2_relat_1(B_73)) | k10_relat_1(B_73, A_72)!=k1_xboole_0 | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_268, c_22])).
% 2.25/1.38  tff(c_427, plain, (![A_72]: (r1_xboole_0('#skF_3', A_72) | k10_relat_1('#skF_4', A_72)!=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_422])).
% 2.25/1.38  tff(c_436, plain, (![A_74]: (r1_xboole_0('#skF_3', A_74) | k10_relat_1('#skF_4', A_74)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_427])).
% 2.25/1.38  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.25/1.38  tff(c_12, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.25/1.38  tff(c_63, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.25/1.38  tff(c_75, plain, (![B_9]: (k4_xboole_0(B_9, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_63])).
% 2.25/1.38  tff(c_97, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.25/1.38  tff(c_115, plain, (![B_9]: (k4_xboole_0(B_9, k1_xboole_0)=k3_xboole_0(B_9, B_9))), inference(superposition, [status(thm), theory('equality')], [c_75, c_97])).
% 2.25/1.38  tff(c_122, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_115])).
% 2.25/1.38  tff(c_172, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.25/1.38  tff(c_178, plain, (![B_9, C_40]: (~r1_xboole_0(B_9, B_9) | ~r2_hidden(C_40, B_9))), inference(superposition, [status(thm), theory('equality')], [c_122, c_172])).
% 2.25/1.38  tff(c_447, plain, (![C_40]: (~r2_hidden(C_40, '#skF_3') | k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_436, c_178])).
% 2.25/1.38  tff(c_453, plain, (![C_40]: (~r2_hidden(C_40, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_447])).
% 2.25/1.38  tff(c_74, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_63])).
% 2.25/1.38  tff(c_112, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_97])).
% 2.25/1.38  tff(c_121, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_112])).
% 2.25/1.38  tff(c_175, plain, (![C_40]: (~r1_xboole_0('#skF_3', k2_relat_1('#skF_4')) | ~r2_hidden(C_40, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_172])).
% 2.25/1.38  tff(c_198, plain, (~r1_xboole_0('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_175])).
% 2.25/1.38  tff(c_215, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), k3_xboole_0(A_51, B_52)) | r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.25/1.38  tff(c_221, plain, (r2_hidden('#skF_1'('#skF_3', k2_relat_1('#skF_4')), '#skF_3') | r1_xboole_0('#skF_3', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_215])).
% 2.25/1.38  tff(c_229, plain, (r2_hidden('#skF_1'('#skF_3', k2_relat_1('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_198, c_221])).
% 2.25/1.38  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_453, c_229])).
% 2.25/1.38  tff(c_458, plain, (![C_75]: (~r2_hidden(C_75, '#skF_3'))), inference(splitRight, [status(thm)], [c_175])).
% 2.25/1.38  tff(c_462, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_458])).
% 2.25/1.38  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_462])).
% 2.25/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.38  
% 2.25/1.38  Inference rules
% 2.25/1.38  ----------------------
% 2.25/1.38  #Ref     : 0
% 2.25/1.38  #Sup     : 100
% 2.25/1.38  #Fact    : 0
% 2.25/1.38  #Define  : 0
% 2.25/1.38  #Split   : 3
% 2.25/1.38  #Chain   : 0
% 2.25/1.38  #Close   : 0
% 2.25/1.38  
% 2.25/1.38  Ordering : KBO
% 2.25/1.38  
% 2.25/1.38  Simplification rules
% 2.25/1.38  ----------------------
% 2.25/1.38  #Subsume      : 13
% 2.25/1.38  #Demod        : 35
% 2.25/1.38  #Tautology    : 51
% 2.25/1.38  #SimpNegUnit  : 5
% 2.25/1.38  #BackRed      : 1
% 2.25/1.38  
% 2.25/1.38  #Partial instantiations: 0
% 2.25/1.38  #Strategies tried      : 1
% 2.25/1.38  
% 2.25/1.38  Timing (in seconds)
% 2.25/1.38  ----------------------
% 2.25/1.38  Preprocessing        : 0.32
% 2.25/1.38  Parsing              : 0.17
% 2.25/1.38  CNF conversion       : 0.02
% 2.25/1.38  Main loop            : 0.24
% 2.25/1.38  Inferencing          : 0.09
% 2.25/1.38  Reduction            : 0.07
% 2.25/1.38  Demodulation         : 0.05
% 2.25/1.38  BG Simplification    : 0.01
% 2.25/1.38  Subsumption          : 0.05
% 2.25/1.38  Abstraction          : 0.01
% 2.25/1.38  MUC search           : 0.00
% 2.25/1.38  Cooper               : 0.00
% 2.25/1.38  Total                : 0.59
% 2.25/1.38  Index Insertion      : 0.00
% 2.25/1.38  Index Deletion       : 0.00
% 2.25/1.38  Index Matching       : 0.00
% 2.25/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
