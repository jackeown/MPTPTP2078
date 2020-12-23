%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:38 EST 2020

% Result     : Theorem 17.07s
% Output     : CNFRefutation 17.07s
% Verified   : 
% Statistics : Number of formulae       :   56 (  62 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 (  87 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_44,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_279,plain,(
    ! [B_62,A_63] :
      ( ~ r2_hidden(B_62,A_63)
      | k4_xboole_0(A_63,k1_tarski(B_62)) != A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_292,plain,(
    ! [B_62] : ~ r2_hidden(B_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_279])).

tff(c_16,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_80,plain,(
    ! [B_12] : k4_xboole_0(B_12,B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_36,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,k1_tarski(B_29)) = A_28
      | r2_hidden(B_29,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_163,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k4_xboole_0(A_54,B_55)) = k3_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_182,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,A_28) = k3_xboole_0(A_28,k1_tarski(B_29))
      | r2_hidden(B_29,A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_163])).

tff(c_195,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,k1_tarski(B_29)) = k1_xboole_0
      | r2_hidden(B_29,A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_182])).

tff(c_630,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_2'(A_102,B_103),k3_xboole_0(A_102,B_103))
      | r1_xboole_0(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_638,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_2'(A_28,k1_tarski(B_29)),k1_xboole_0)
      | r1_xboole_0(A_28,k1_tarski(B_29))
      | r2_hidden(B_29,A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_630])).

tff(c_669,plain,(
    ! [A_105,B_106] :
      ( r1_xboole_0(A_105,k1_tarski(B_106))
      | r2_hidden(B_106,A_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_638])).

tff(c_40,plain,(
    ! [B_33,A_32] :
      ( k10_relat_1(B_33,A_32) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_33),A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3737,plain,(
    ! [B_246,B_247] :
      ( k10_relat_1(B_246,k1_tarski(B_247)) = k1_xboole_0
      | ~ v1_relat_1(B_246)
      | r2_hidden(B_247,k2_relat_1(B_246)) ) ),
    inference(resolution,[status(thm)],[c_669,c_40])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47326,plain,(
    ! [A_938,B_939] :
      ( r1_tarski(A_938,k2_relat_1(B_939))
      | k10_relat_1(B_939,k1_tarski('#skF_1'(A_938,k2_relat_1(B_939)))) = k1_xboole_0
      | ~ v1_relat_1(B_939) ) ),
    inference(resolution,[status(thm)],[c_3737,c_4])).

tff(c_46,plain,(
    ! [C_35] :
      ( k10_relat_1('#skF_4',k1_tarski(C_35)) != k1_xboole_0
      | ~ r2_hidden(C_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_47337,plain,(
    ! [A_938] :
      ( ~ r2_hidden('#skF_1'(A_938,k2_relat_1('#skF_4')),'#skF_3')
      | r1_tarski(A_938,k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47326,c_46])).

tff(c_47358,plain,(
    ! [A_940] :
      ( ~ r2_hidden('#skF_1'(A_940,k2_relat_1('#skF_4')),'#skF_3')
      | r1_tarski(A_940,k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_47337])).

tff(c_47386,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_47358])).

tff(c_47397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_47386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:33:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.07/8.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.07/8.22  
% 17.07/8.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.07/8.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 17.07/8.22  
% 17.07/8.22  %Foreground sorts:
% 17.07/8.22  
% 17.07/8.22  
% 17.07/8.22  %Background operators:
% 17.07/8.22  
% 17.07/8.22  
% 17.07/8.22  %Foreground operators:
% 17.07/8.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.07/8.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.07/8.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.07/8.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.07/8.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.07/8.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.07/8.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.07/8.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.07/8.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.07/8.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.07/8.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.07/8.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.07/8.22  tff('#skF_3', type, '#skF_3': $i).
% 17.07/8.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.07/8.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 17.07/8.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.07/8.22  tff('#skF_4', type, '#skF_4': $i).
% 17.07/8.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.07/8.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.07/8.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.07/8.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.07/8.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.07/8.22  
% 17.07/8.23  tff(f_92, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_1)).
% 17.07/8.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 17.07/8.23  tff(f_60, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 17.07/8.23  tff(f_73, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 17.07/8.23  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.07/8.23  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 17.07/8.23  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 17.07/8.23  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 17.07/8.23  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 17.07/8.23  tff(c_44, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.07/8.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.07/8.23  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.07/8.23  tff(c_24, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.07/8.23  tff(c_279, plain, (![B_62, A_63]: (~r2_hidden(B_62, A_63) | k4_xboole_0(A_63, k1_tarski(B_62))!=A_63)), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.07/8.23  tff(c_292, plain, (![B_62]: (~r2_hidden(B_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_279])).
% 17.07/8.23  tff(c_16, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.07/8.23  tff(c_76, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 17.07/8.23  tff(c_80, plain, (![B_12]: (k4_xboole_0(B_12, B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_76])).
% 17.07/8.23  tff(c_36, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k1_tarski(B_29))=A_28 | r2_hidden(B_29, A_28))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.07/8.23  tff(c_163, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k4_xboole_0(A_54, B_55))=k3_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.07/8.23  tff(c_182, plain, (![A_28, B_29]: (k4_xboole_0(A_28, A_28)=k3_xboole_0(A_28, k1_tarski(B_29)) | r2_hidden(B_29, A_28))), inference(superposition, [status(thm), theory('equality')], [c_36, c_163])).
% 17.07/8.23  tff(c_195, plain, (![A_28, B_29]: (k3_xboole_0(A_28, k1_tarski(B_29))=k1_xboole_0 | r2_hidden(B_29, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_182])).
% 17.07/8.23  tff(c_630, plain, (![A_102, B_103]: (r2_hidden('#skF_2'(A_102, B_103), k3_xboole_0(A_102, B_103)) | r1_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.07/8.23  tff(c_638, plain, (![A_28, B_29]: (r2_hidden('#skF_2'(A_28, k1_tarski(B_29)), k1_xboole_0) | r1_xboole_0(A_28, k1_tarski(B_29)) | r2_hidden(B_29, A_28))), inference(superposition, [status(thm), theory('equality')], [c_195, c_630])).
% 17.07/8.23  tff(c_669, plain, (![A_105, B_106]: (r1_xboole_0(A_105, k1_tarski(B_106)) | r2_hidden(B_106, A_105))), inference(negUnitSimplification, [status(thm)], [c_292, c_638])).
% 17.07/8.23  tff(c_40, plain, (![B_33, A_32]: (k10_relat_1(B_33, A_32)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_33), A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.07/8.23  tff(c_3737, plain, (![B_246, B_247]: (k10_relat_1(B_246, k1_tarski(B_247))=k1_xboole_0 | ~v1_relat_1(B_246) | r2_hidden(B_247, k2_relat_1(B_246)))), inference(resolution, [status(thm)], [c_669, c_40])).
% 17.07/8.23  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.07/8.23  tff(c_47326, plain, (![A_938, B_939]: (r1_tarski(A_938, k2_relat_1(B_939)) | k10_relat_1(B_939, k1_tarski('#skF_1'(A_938, k2_relat_1(B_939))))=k1_xboole_0 | ~v1_relat_1(B_939))), inference(resolution, [status(thm)], [c_3737, c_4])).
% 17.07/8.23  tff(c_46, plain, (![C_35]: (k10_relat_1('#skF_4', k1_tarski(C_35))!=k1_xboole_0 | ~r2_hidden(C_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.07/8.23  tff(c_47337, plain, (![A_938]: (~r2_hidden('#skF_1'(A_938, k2_relat_1('#skF_4')), '#skF_3') | r1_tarski(A_938, k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_47326, c_46])).
% 17.07/8.23  tff(c_47358, plain, (![A_940]: (~r2_hidden('#skF_1'(A_940, k2_relat_1('#skF_4')), '#skF_3') | r1_tarski(A_940, k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_47337])).
% 17.07/8.23  tff(c_47386, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_47358])).
% 17.07/8.23  tff(c_47397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_47386])).
% 17.07/8.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.07/8.23  
% 17.07/8.23  Inference rules
% 17.07/8.23  ----------------------
% 17.07/8.23  #Ref     : 0
% 17.07/8.23  #Sup     : 12006
% 17.07/8.23  #Fact    : 4
% 17.07/8.23  #Define  : 0
% 17.07/8.23  #Split   : 5
% 17.07/8.23  #Chain   : 0
% 17.07/8.23  #Close   : 0
% 17.07/8.23  
% 17.07/8.23  Ordering : KBO
% 17.07/8.23  
% 17.07/8.23  Simplification rules
% 17.07/8.23  ----------------------
% 17.07/8.23  #Subsume      : 5210
% 17.07/8.23  #Demod        : 5536
% 17.07/8.23  #Tautology    : 1695
% 17.07/8.23  #SimpNegUnit  : 196
% 17.07/8.23  #BackRed      : 43
% 17.07/8.23  
% 17.07/8.23  #Partial instantiations: 0
% 17.07/8.23  #Strategies tried      : 1
% 17.07/8.23  
% 17.07/8.23  Timing (in seconds)
% 17.07/8.23  ----------------------
% 17.07/8.24  Preprocessing        : 0.40
% 17.07/8.24  Parsing              : 0.19
% 17.07/8.24  CNF conversion       : 0.03
% 17.07/8.24  Main loop            : 6.95
% 17.07/8.24  Inferencing          : 1.19
% 17.07/8.24  Reduction            : 2.21
% 17.07/8.24  Demodulation         : 1.70
% 17.07/8.24  BG Simplification    : 0.14
% 17.07/8.24  Subsumption          : 3.04
% 17.07/8.24  Abstraction          : 0.22
% 17.07/8.24  MUC search           : 0.00
% 17.07/8.24  Cooper               : 0.00
% 17.07/8.24  Total                : 7.39
% 17.07/8.24  Index Insertion      : 0.00
% 17.07/8.24  Index Deletion       : 0.00
% 17.07/8.24  Index Matching       : 0.00
% 17.07/8.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
