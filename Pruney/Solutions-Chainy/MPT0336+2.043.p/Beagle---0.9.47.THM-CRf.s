%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:06 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 114 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 189 expanded)
%              Number of equality atoms :    6 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_58,axiom,(
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

tff(f_103,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_4'(A_16,B_17),k3_xboole_0(A_16,B_17))
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    r1_tarski(k3_xboole_0('#skF_5','#skF_6'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_59,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_5'),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_152,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_156,plain,(
    k3_xboole_0(k3_xboole_0('#skF_6','#skF_5'),k1_tarski('#skF_8')) = k3_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_59,c_152])).

tff(c_217,plain,(
    ! [D_65,B_66,A_67] :
      ( r2_hidden(D_65,B_66)
      | ~ r2_hidden(D_65,k3_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_598,plain,(
    ! [D_116] :
      ( r2_hidden(D_116,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_116,k3_xboole_0('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_217])).

tff(c_626,plain,
    ( r2_hidden('#skF_4'('#skF_6','#skF_5'),k1_tarski('#skF_8'))
    | r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_598])).

tff(c_629,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_626])).

tff(c_54,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_69,plain,(
    ! [B_37,A_38] :
      ( r1_xboole_0(B_37,A_38)
      | ~ r1_xboole_0(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_69])).

tff(c_643,plain,(
    ! [A_117,C_118,B_119] :
      ( ~ r1_xboole_0(A_117,C_118)
      | ~ r1_xboole_0(A_117,B_119)
      | r1_xboole_0(A_117,k2_xboole_0(B_119,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1979,plain,(
    ! [B_180,C_181,A_182] :
      ( r1_xboole_0(k2_xboole_0(B_180,C_181),A_182)
      | ~ r1_xboole_0(A_182,C_181)
      | ~ r1_xboole_0(A_182,B_180) ) ),
    inference(resolution,[status(thm)],[c_643,c_22])).

tff(c_52,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_5','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2004,plain,
    ( ~ r1_xboole_0('#skF_6','#skF_7')
    | ~ r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1979,c_52])).

tff(c_2018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_72,c_2004])).

tff(c_2020,plain,(
    ~ r1_xboole_0('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_626])).

tff(c_56,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_374,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | ~ r2_hidden(C_90,B_89)
      | ~ r2_hidden(C_90,A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_396,plain,(
    ! [C_91] :
      ( ~ r2_hidden(C_91,'#skF_6')
      | ~ r2_hidden(C_91,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_374])).

tff(c_410,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_396])).

tff(c_48,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_171,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,k3_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_257,plain,(
    ! [B_71,A_72,C_73] :
      ( ~ r1_xboole_0(B_71,A_72)
      | ~ r2_hidden(C_73,k3_xboole_0(A_72,B_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_171])).

tff(c_260,plain,(
    ! [C_73] :
      ( ~ r1_xboole_0(k1_tarski('#skF_8'),k3_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_73,k3_xboole_0('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_257])).

tff(c_2111,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_8'),k3_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_2123,plain,(
    r2_hidden('#skF_8',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_2111])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2134,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_2123,c_8])).

tff(c_2147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_2134])).

tff(c_2150,plain,(
    ! [C_192] : ~ r2_hidden(C_192,k3_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_2170,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_2150])).

tff(c_2186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2020,c_2170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:37:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/2.25  
% 4.56/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/2.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 4.56/2.25  
% 4.56/2.25  %Foreground sorts:
% 4.56/2.25  
% 4.56/2.25  
% 4.56/2.25  %Background operators:
% 4.56/2.25  
% 4.56/2.25  
% 4.56/2.25  %Foreground operators:
% 4.56/2.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.56/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.56/2.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.56/2.25  tff('#skF_7', type, '#skF_7': $i).
% 4.56/2.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.56/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.56/2.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.56/2.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.56/2.25  tff('#skF_5', type, '#skF_5': $i).
% 4.56/2.25  tff('#skF_6', type, '#skF_6': $i).
% 4.56/2.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.56/2.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.56/2.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.56/2.25  tff('#skF_8', type, '#skF_8': $i).
% 4.56/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/2.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.56/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/2.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.56/2.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.56/2.25  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.56/2.25  
% 4.56/2.26  tff(f_72, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.56/2.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.56/2.26  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.56/2.26  tff(f_76, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.56/2.26  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.56/2.26  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.56/2.26  tff(f_92, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.56/2.26  tff(f_58, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.56/2.26  tff(f_103, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.56/2.26  tff(c_30, plain, (![A_16, B_17]: (r2_hidden('#skF_4'(A_16, B_17), k3_xboole_0(A_16, B_17)) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.56/2.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.56/2.26  tff(c_58, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.56/2.26  tff(c_59, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_5'), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58])).
% 4.56/2.26  tff(c_152, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.56/2.26  tff(c_156, plain, (k3_xboole_0(k3_xboole_0('#skF_6', '#skF_5'), k1_tarski('#skF_8'))=k3_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_59, c_152])).
% 4.56/2.26  tff(c_217, plain, (![D_65, B_66, A_67]: (r2_hidden(D_65, B_66) | ~r2_hidden(D_65, k3_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.56/2.26  tff(c_598, plain, (![D_116]: (r2_hidden(D_116, k1_tarski('#skF_8')) | ~r2_hidden(D_116, k3_xboole_0('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_156, c_217])).
% 4.56/2.26  tff(c_626, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_5'), k1_tarski('#skF_8')) | r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_598])).
% 4.56/2.26  tff(c_629, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_626])).
% 4.56/2.26  tff(c_54, plain, (r1_xboole_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.56/2.26  tff(c_69, plain, (![B_37, A_38]: (r1_xboole_0(B_37, A_38) | ~r1_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.56/2.26  tff(c_72, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_69])).
% 4.56/2.26  tff(c_643, plain, (![A_117, C_118, B_119]: (~r1_xboole_0(A_117, C_118) | ~r1_xboole_0(A_117, B_119) | r1_xboole_0(A_117, k2_xboole_0(B_119, C_118)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.56/2.26  tff(c_22, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.56/2.26  tff(c_1979, plain, (![B_180, C_181, A_182]: (r1_xboole_0(k2_xboole_0(B_180, C_181), A_182) | ~r1_xboole_0(A_182, C_181) | ~r1_xboole_0(A_182, B_180))), inference(resolution, [status(thm)], [c_643, c_22])).
% 4.56/2.26  tff(c_52, plain, (~r1_xboole_0(k2_xboole_0('#skF_5', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.56/2.26  tff(c_2004, plain, (~r1_xboole_0('#skF_6', '#skF_7') | ~r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1979, c_52])).
% 4.56/2.26  tff(c_2018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_629, c_72, c_2004])).
% 4.56/2.26  tff(c_2020, plain, (~r1_xboole_0('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_626])).
% 4.56/2.26  tff(c_56, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.56/2.26  tff(c_374, plain, (![A_88, B_89, C_90]: (~r1_xboole_0(A_88, B_89) | ~r2_hidden(C_90, B_89) | ~r2_hidden(C_90, A_88))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.56/2.26  tff(c_396, plain, (![C_91]: (~r2_hidden(C_91, '#skF_6') | ~r2_hidden(C_91, '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_374])).
% 4.56/2.26  tff(c_410, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_396])).
% 4.56/2.26  tff(c_48, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.56/2.26  tff(c_171, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.56/2.26  tff(c_257, plain, (![B_71, A_72, C_73]: (~r1_xboole_0(B_71, A_72) | ~r2_hidden(C_73, k3_xboole_0(A_72, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_171])).
% 4.56/2.26  tff(c_260, plain, (![C_73]: (~r1_xboole_0(k1_tarski('#skF_8'), k3_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(C_73, k3_xboole_0('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_156, c_257])).
% 4.56/2.26  tff(c_2111, plain, (~r1_xboole_0(k1_tarski('#skF_8'), k3_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_260])).
% 4.56/2.26  tff(c_2123, plain, (r2_hidden('#skF_8', k3_xboole_0('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_2111])).
% 4.56/2.26  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.56/2.26  tff(c_2134, plain, (r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_2123, c_8])).
% 4.56/2.26  tff(c_2147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_410, c_2134])).
% 4.56/2.26  tff(c_2150, plain, (![C_192]: (~r2_hidden(C_192, k3_xboole_0('#skF_6', '#skF_5')))), inference(splitRight, [status(thm)], [c_260])).
% 4.56/2.26  tff(c_2170, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_2150])).
% 4.56/2.26  tff(c_2186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2020, c_2170])).
% 4.56/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/2.26  
% 4.56/2.26  Inference rules
% 4.56/2.26  ----------------------
% 4.56/2.26  #Ref     : 0
% 4.56/2.26  #Sup     : 486
% 4.56/2.26  #Fact    : 0
% 4.56/2.26  #Define  : 0
% 4.56/2.26  #Split   : 7
% 4.56/2.26  #Chain   : 0
% 4.56/2.26  #Close   : 0
% 4.56/2.26  
% 4.56/2.26  Ordering : KBO
% 4.56/2.26  
% 4.56/2.26  Simplification rules
% 4.56/2.26  ----------------------
% 4.56/2.26  #Subsume      : 125
% 4.56/2.26  #Demod        : 125
% 4.56/2.26  #Tautology    : 142
% 4.56/2.26  #SimpNegUnit  : 28
% 4.56/2.26  #BackRed      : 1
% 4.56/2.26  
% 4.56/2.26  #Partial instantiations: 0
% 4.56/2.26  #Strategies tried      : 1
% 4.56/2.26  
% 4.56/2.26  Timing (in seconds)
% 4.56/2.26  ----------------------
% 4.56/2.27  Preprocessing        : 0.54
% 4.56/2.27  Parsing              : 0.27
% 4.56/2.27  CNF conversion       : 0.04
% 4.56/2.27  Main loop            : 0.79
% 4.56/2.27  Inferencing          : 0.26
% 4.56/2.27  Reduction            : 0.26
% 4.56/2.27  Demodulation         : 0.20
% 4.56/2.27  BG Simplification    : 0.04
% 4.56/2.27  Subsumption          : 0.17
% 4.56/2.27  Abstraction          : 0.04
% 4.56/2.27  MUC search           : 0.00
% 4.56/2.27  Cooper               : 0.00
% 4.56/2.27  Total                : 1.36
% 4.56/2.27  Index Insertion      : 0.00
% 4.56/2.27  Index Deletion       : 0.00
% 4.56/2.27  Index Matching       : 0.00
% 4.56/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
