%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:39 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 147 expanded)
%              Number of leaves         :   32 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :   64 ( 175 expanded)
%              Number of equality atoms :   25 (  72 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_68,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_55,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_54])).

tff(c_126,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(k2_xboole_0(B_49,A_50))
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_129,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_126])).

tff(c_131,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_129])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_135,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_131,c_4])).

tff(c_22,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_140,plain,(
    ! [A_14] : r1_xboole_0(A_14,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_22])).

tff(c_10,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_2'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_136,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_2'(A_7),A_7)
      | A_7 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_10])).

tff(c_217,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_482,plain,(
    ! [A_76,B_77] :
      ( ~ r1_xboole_0(A_76,B_77)
      | k3_xboole_0(A_76,B_77) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_136,c_217])).

tff(c_487,plain,(
    ! [A_78] : k3_xboole_0(A_78,'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_140,c_482])).

tff(c_8,plain,(
    ! [A_2,B_3,C_6] :
      ( ~ r1_xboole_0(A_2,B_3)
      | ~ r2_hidden(C_6,k3_xboole_0(A_2,B_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_492,plain,(
    ! [A_78,C_6] :
      ( ~ r1_xboole_0(A_78,'#skF_7')
      | ~ r2_hidden(C_6,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_8])).

tff(c_497,plain,(
    ! [C_6] : ~ r2_hidden(C_6,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_492])).

tff(c_148,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_194,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(B_60,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_148])).

tff(c_52,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_223,plain,(
    ! [B_64,A_65] : k2_xboole_0(B_64,A_65) = k2_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_52])).

tff(c_138,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_55])).

tff(c_241,plain,(
    k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_138])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( ~ v1_xboole_0(k2_xboole_0(B_12,A_11))
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_300,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0(k2_tarski('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_18])).

tff(c_308,plain,(
    v1_xboole_0(k2_tarski('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_300])).

tff(c_139,plain,(
    ! [A_1] :
      ( A_1 = '#skF_7'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_4])).

tff(c_314,plain,(
    k2_tarski('#skF_6','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_308,c_139])).

tff(c_32,plain,(
    ! [D_24,B_20] : r2_hidden(D_24,k2_tarski(D_24,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_333,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_32])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:59:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.22/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.22/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.22/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.31  
% 2.52/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.52/1.33  tff(f_72, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.52/1.33  tff(f_93, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.52/1.33  tff(f_64, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.52/1.33  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.52/1.33  tff(f_68, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.52/1.33  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.52/1.33  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.52/1.33  tff(f_89, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.52/1.33  tff(f_81, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.52/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.52/1.33  tff(c_26, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.33  tff(c_54, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.52/1.33  tff(c_55, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_54])).
% 2.52/1.33  tff(c_126, plain, (![B_49, A_50]: (~v1_xboole_0(k2_xboole_0(B_49, A_50)) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.52/1.33  tff(c_129, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_55, c_126])).
% 2.52/1.33  tff(c_131, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_129])).
% 2.52/1.33  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.52/1.33  tff(c_135, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_131, c_4])).
% 2.52/1.33  tff(c_22, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.52/1.33  tff(c_140, plain, (![A_14]: (r1_xboole_0(A_14, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_22])).
% 2.52/1.33  tff(c_10, plain, (![A_7]: (r2_hidden('#skF_2'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.52/1.33  tff(c_136, plain, (![A_7]: (r2_hidden('#skF_2'(A_7), A_7) | A_7='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_10])).
% 2.52/1.33  tff(c_217, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.33  tff(c_482, plain, (![A_76, B_77]: (~r1_xboole_0(A_76, B_77) | k3_xboole_0(A_76, B_77)='#skF_7')), inference(resolution, [status(thm)], [c_136, c_217])).
% 2.52/1.33  tff(c_487, plain, (![A_78]: (k3_xboole_0(A_78, '#skF_7')='#skF_7')), inference(resolution, [status(thm)], [c_140, c_482])).
% 2.52/1.33  tff(c_8, plain, (![A_2, B_3, C_6]: (~r1_xboole_0(A_2, B_3) | ~r2_hidden(C_6, k3_xboole_0(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.52/1.33  tff(c_492, plain, (![A_78, C_6]: (~r1_xboole_0(A_78, '#skF_7') | ~r2_hidden(C_6, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_8])).
% 2.52/1.33  tff(c_497, plain, (![C_6]: (~r2_hidden(C_6, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_492])).
% 2.52/1.33  tff(c_148, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.52/1.33  tff(c_194, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(B_60, A_59))), inference(superposition, [status(thm), theory('equality')], [c_26, c_148])).
% 2.52/1.33  tff(c_52, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.52/1.33  tff(c_223, plain, (![B_64, A_65]: (k2_xboole_0(B_64, A_65)=k2_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_194, c_52])).
% 2.52/1.33  tff(c_138, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_55])).
% 2.52/1.33  tff(c_241, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_223, c_138])).
% 2.52/1.33  tff(c_18, plain, (![B_12, A_11]: (~v1_xboole_0(k2_xboole_0(B_12, A_11)) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.52/1.33  tff(c_300, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0(k2_tarski('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_18])).
% 2.52/1.33  tff(c_308, plain, (v1_xboole_0(k2_tarski('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_300])).
% 2.52/1.33  tff(c_139, plain, (![A_1]: (A_1='#skF_7' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_4])).
% 2.52/1.33  tff(c_314, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_308, c_139])).
% 2.52/1.33  tff(c_32, plain, (![D_24, B_20]: (r2_hidden(D_24, k2_tarski(D_24, B_20)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.52/1.33  tff(c_333, plain, (r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_314, c_32])).
% 2.52/1.33  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_497, c_333])).
% 2.52/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  Inference rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Ref     : 0
% 2.52/1.33  #Sup     : 113
% 2.52/1.33  #Fact    : 0
% 2.52/1.33  #Define  : 0
% 2.52/1.33  #Split   : 1
% 2.52/1.33  #Chain   : 0
% 2.52/1.33  #Close   : 0
% 2.52/1.33  
% 2.52/1.33  Ordering : KBO
% 2.52/1.33  
% 2.52/1.33  Simplification rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Subsume      : 7
% 2.52/1.33  #Demod        : 55
% 2.52/1.33  #Tautology    : 82
% 2.52/1.33  #SimpNegUnit  : 2
% 2.52/1.33  #BackRed      : 13
% 2.52/1.33  
% 2.52/1.33  #Partial instantiations: 0
% 2.52/1.33  #Strategies tried      : 1
% 2.52/1.33  
% 2.52/1.33  Timing (in seconds)
% 2.52/1.33  ----------------------
% 2.52/1.33  Preprocessing        : 0.32
% 2.52/1.33  Parsing              : 0.17
% 2.52/1.33  CNF conversion       : 0.02
% 2.52/1.33  Main loop            : 0.25
% 2.52/1.33  Inferencing          : 0.08
% 2.52/1.33  Reduction            : 0.09
% 2.52/1.33  Demodulation         : 0.07
% 2.52/1.33  BG Simplification    : 0.02
% 2.52/1.33  Subsumption          : 0.05
% 2.52/1.33  Abstraction          : 0.02
% 2.52/1.33  MUC search           : 0.00
% 2.52/1.33  Cooper               : 0.00
% 2.52/1.33  Total                : 0.60
% 2.52/1.33  Index Insertion      : 0.00
% 2.52/1.33  Index Deletion       : 0.00
% 2.52/1.33  Index Matching       : 0.00
% 2.52/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
