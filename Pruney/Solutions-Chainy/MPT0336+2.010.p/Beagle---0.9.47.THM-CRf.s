%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:01 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 112 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 196 expanded)
%              Number of equality atoms :    6 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),k3_xboole_0(A_13,B_14))
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_151,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_155,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_151])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_530,plain,(
    ! [D_106] :
      ( r2_hidden(D_106,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_106,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_8])).

tff(c_545,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),k1_tarski('#skF_7'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_530])).

tff(c_772,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_778,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_772,c_24])).

tff(c_50,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_64,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(B_35,A_36)
      | ~ r1_xboole_0(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_64])).

tff(c_512,plain,(
    ! [A_103,C_104,B_105] :
      ( ~ r1_xboole_0(A_103,C_104)
      | ~ r1_xboole_0(A_103,B_105)
      | r1_xboole_0(A_103,k2_xboole_0(B_105,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1870,plain,(
    ! [B_200,C_201,A_202] :
      ( r1_xboole_0(k2_xboole_0(B_200,C_201),A_202)
      | ~ r1_xboole_0(A_202,C_201)
      | ~ r1_xboole_0(A_202,B_200) ) ),
    inference(resolution,[status(thm)],[c_512,c_24])).

tff(c_48,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1893,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1870,c_48])).

tff(c_1911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_67,c_1893])).

tff(c_1913,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_52,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_191,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | r1_xboole_0(A_58,k3_xboole_0(B_59,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_199,plain,(
    ! [A_58,B_4,A_3] :
      ( ~ r1_xboole_0(A_58,B_4)
      | r1_xboole_0(A_58,k3_xboole_0(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_191])).

tff(c_160,plain,(
    ! [A_49,B_50,C_51] :
      ( ~ r1_xboole_0(A_49,B_50)
      | ~ r2_hidden(C_51,k3_xboole_0(A_49,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_279,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(C_75,k3_xboole_0(B_74,A_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_160])).

tff(c_282,plain,(
    ! [C_75] :
      ( ~ r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5'))
      | ~ r2_hidden(C_75,k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_279])).

tff(c_1948,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_1974,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_199,c_1948])).

tff(c_1980,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1974])).

tff(c_554,plain,(
    ! [D_110,A_111,B_112] :
      ( r2_hidden(D_110,k3_xboole_0(A_111,B_112))
      | ~ r2_hidden(D_110,B_112)
      | ~ r2_hidden(D_110,A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_13,B_14,C_17] :
      ( ~ r1_xboole_0(A_13,B_14)
      | ~ r2_hidden(C_17,k3_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_588,plain,(
    ! [A_113,B_114,D_115] :
      ( ~ r1_xboole_0(A_113,B_114)
      | ~ r2_hidden(D_115,B_114)
      | ~ r2_hidden(D_115,A_113) ) ),
    inference(resolution,[status(thm)],[c_554,c_28])).

tff(c_626,plain,(
    ! [D_115] :
      ( ~ r2_hidden(D_115,'#skF_6')
      | ~ r2_hidden(D_115,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_67,c_588])).

tff(c_1983,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_1980,c_626])).

tff(c_1987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1983])).

tff(c_1990,plain,(
    ! [C_205] : ~ r2_hidden(C_205,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_2018,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_1990])).

tff(c_2028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1913,c_2018])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.65  
% 3.72/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.65  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.72/1.65  
% 3.72/1.65  %Foreground sorts:
% 3.72/1.65  
% 3.72/1.65  
% 3.72/1.65  %Background operators:
% 3.72/1.65  
% 3.72/1.65  
% 3.72/1.65  %Foreground operators:
% 3.72/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.72/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.72/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.72/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.72/1.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.72/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.72/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.72/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.72/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.72/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.72/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.72/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.72/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.72/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.72/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.72/1.65  
% 3.72/1.66  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.72/1.66  tff(f_102, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.72/1.66  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.72/1.66  tff(f_38, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.72/1.66  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.72/1.66  tff(f_76, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.72/1.66  tff(f_93, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.72/1.66  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.72/1.66  tff(f_82, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.72/1.66  tff(c_26, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), k3_xboole_0(A_13, B_14)) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.72/1.66  tff(c_54, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.72/1.66  tff(c_151, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.72/1.66  tff(c_155, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_151])).
% 3.72/1.66  tff(c_8, plain, (![D_10, B_6, A_5]: (r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.72/1.66  tff(c_530, plain, (![D_106]: (r2_hidden(D_106, k1_tarski('#skF_7')) | ~r2_hidden(D_106, k3_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_155, c_8])).
% 3.72/1.66  tff(c_545, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), k1_tarski('#skF_7')) | r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_530])).
% 3.72/1.66  tff(c_772, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_545])).
% 3.72/1.66  tff(c_24, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.72/1.66  tff(c_778, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_772, c_24])).
% 3.72/1.66  tff(c_50, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.72/1.66  tff(c_64, plain, (![B_35, A_36]: (r1_xboole_0(B_35, A_36) | ~r1_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.72/1.66  tff(c_67, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_64])).
% 3.72/1.66  tff(c_512, plain, (![A_103, C_104, B_105]: (~r1_xboole_0(A_103, C_104) | ~r1_xboole_0(A_103, B_105) | r1_xboole_0(A_103, k2_xboole_0(B_105, C_104)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.72/1.66  tff(c_1870, plain, (![B_200, C_201, A_202]: (r1_xboole_0(k2_xboole_0(B_200, C_201), A_202) | ~r1_xboole_0(A_202, C_201) | ~r1_xboole_0(A_202, B_200))), inference(resolution, [status(thm)], [c_512, c_24])).
% 3.72/1.66  tff(c_48, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.72/1.66  tff(c_1893, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1870, c_48])).
% 3.72/1.66  tff(c_1911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_778, c_67, c_1893])).
% 3.72/1.66  tff(c_1913, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_545])).
% 3.72/1.66  tff(c_52, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.72/1.66  tff(c_46, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.72/1.66  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.66  tff(c_191, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | r1_xboole_0(A_58, k3_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.72/1.66  tff(c_199, plain, (![A_58, B_4, A_3]: (~r1_xboole_0(A_58, B_4) | r1_xboole_0(A_58, k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_191])).
% 3.72/1.66  tff(c_160, plain, (![A_49, B_50, C_51]: (~r1_xboole_0(A_49, B_50) | ~r2_hidden(C_51, k3_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.72/1.66  tff(c_279, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(C_75, k3_xboole_0(B_74, A_73)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_160])).
% 3.72/1.66  tff(c_282, plain, (![C_75]: (~r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5')) | ~r2_hidden(C_75, k3_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_155, c_279])).
% 3.72/1.66  tff(c_1948, plain, (~r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_282])).
% 3.72/1.66  tff(c_1974, plain, (~r1_xboole_0(k1_tarski('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_199, c_1948])).
% 3.72/1.66  tff(c_1980, plain, (r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_1974])).
% 3.72/1.66  tff(c_554, plain, (![D_110, A_111, B_112]: (r2_hidden(D_110, k3_xboole_0(A_111, B_112)) | ~r2_hidden(D_110, B_112) | ~r2_hidden(D_110, A_111))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.72/1.66  tff(c_28, plain, (![A_13, B_14, C_17]: (~r1_xboole_0(A_13, B_14) | ~r2_hidden(C_17, k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.72/1.66  tff(c_588, plain, (![A_113, B_114, D_115]: (~r1_xboole_0(A_113, B_114) | ~r2_hidden(D_115, B_114) | ~r2_hidden(D_115, A_113))), inference(resolution, [status(thm)], [c_554, c_28])).
% 3.72/1.66  tff(c_626, plain, (![D_115]: (~r2_hidden(D_115, '#skF_6') | ~r2_hidden(D_115, '#skF_5'))), inference(resolution, [status(thm)], [c_67, c_588])).
% 3.72/1.66  tff(c_1983, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_1980, c_626])).
% 3.72/1.66  tff(c_1987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1983])).
% 3.72/1.66  tff(c_1990, plain, (![C_205]: (~r2_hidden(C_205, k3_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_282])).
% 3.72/1.66  tff(c_2018, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_1990])).
% 3.72/1.66  tff(c_2028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1913, c_2018])).
% 3.72/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.66  
% 3.72/1.66  Inference rules
% 3.72/1.66  ----------------------
% 3.72/1.66  #Ref     : 0
% 3.72/1.66  #Sup     : 471
% 3.72/1.66  #Fact    : 0
% 3.72/1.66  #Define  : 0
% 3.72/1.66  #Split   : 3
% 3.72/1.66  #Chain   : 0
% 3.72/1.66  #Close   : 0
% 3.72/1.66  
% 3.72/1.66  Ordering : KBO
% 3.72/1.66  
% 3.72/1.66  Simplification rules
% 3.72/1.66  ----------------------
% 3.72/1.66  #Subsume      : 121
% 3.72/1.66  #Demod        : 133
% 3.72/1.66  #Tautology    : 125
% 3.72/1.66  #SimpNegUnit  : 11
% 3.72/1.66  #BackRed      : 0
% 3.72/1.66  
% 3.72/1.66  #Partial instantiations: 0
% 3.72/1.66  #Strategies tried      : 1
% 3.72/1.66  
% 3.72/1.66  Timing (in seconds)
% 3.72/1.66  ----------------------
% 3.72/1.67  Preprocessing        : 0.31
% 3.72/1.67  Parsing              : 0.16
% 3.72/1.67  CNF conversion       : 0.02
% 3.72/1.67  Main loop            : 0.56
% 3.72/1.67  Inferencing          : 0.18
% 3.72/1.67  Reduction            : 0.18
% 3.72/1.67  Demodulation         : 0.14
% 3.72/1.67  BG Simplification    : 0.03
% 3.72/1.67  Subsumption          : 0.13
% 3.72/1.67  Abstraction          : 0.03
% 3.72/1.67  MUC search           : 0.00
% 3.72/1.67  Cooper               : 0.00
% 3.72/1.67  Total                : 0.90
% 3.72/1.67  Index Insertion      : 0.00
% 3.72/1.67  Index Deletion       : 0.00
% 3.72/1.67  Index Matching       : 0.00
% 3.72/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
