%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:28 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 127 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 ( 162 expanded)
%              Number of equality atoms :   33 ( 101 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_mcart_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_51,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    ! [B_36] : k3_xboole_0(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [B_37] : k3_xboole_0(k1_xboole_0,B_37) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_12])).

tff(c_8,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [B_37,C_7] :
      ( ~ r1_xboole_0(k1_xboole_0,B_37)
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_8])).

tff(c_90,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_106,plain,(
    ! [B_41,A_42] :
      ( r2_hidden(B_41,A_42)
      | k3_xboole_0(A_42,k1_tarski(B_41)) != k1_tarski(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_113,plain,(
    ! [B_41] :
      ( r2_hidden(B_41,k1_xboole_0)
      | k1_tarski(B_41) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_106])).

tff(c_114,plain,(
    ! [B_41] : k1_tarski(B_41) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_113])).

tff(c_20,plain,(
    ! [A_15,B_16] : k2_zfmisc_1(k1_tarski(A_15),k1_tarski(B_16)) = k1_tarski(k4_tarski(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_180,plain,(
    ! [A_56,B_57] :
      ( k1_relat_1(k2_zfmisc_1(A_56,B_57)) = A_56
      | k1_xboole_0 = B_57
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_189,plain,(
    ! [A_15,B_16] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_15,B_16))) = k1_tarski(A_15)
      | k1_tarski(B_16) = k1_xboole_0
      | k1_tarski(A_15) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_180])).

tff(c_192,plain,(
    ! [A_15,B_16] : k1_relat_1(k1_tarski(k4_tarski(A_15,B_16))) = k1_tarski(A_15) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_114,c_189])).

tff(c_28,plain,(
    ! [A_21,B_22,C_23] : k4_tarski(k4_tarski(A_21,B_22),C_23) = k3_mcart_1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_193,plain,(
    ! [A_58,B_59] : k1_relat_1(k1_tarski(k4_tarski(A_58,B_59))) = k1_tarski(A_58) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_114,c_189])).

tff(c_202,plain,(
    ! [A_21,B_22,C_23] : k1_relat_1(k1_tarski(k3_mcart_1(A_21,B_22,C_23))) = k1_tarski(k4_tarski(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_193])).

tff(c_30,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_2','#skF_3','#skF_4')))) != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_273,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_2','#skF_3'))) != k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_30])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_273])).

tff(c_278,plain,(
    ! [B_67] : ~ r1_xboole_0(k1_xboole_0,B_67) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_282,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_278])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:12:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.20  
% 2.00/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.20  %$ r2_hidden > r1_xboole_0 > k3_mcart_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.00/1.20  
% 2.00/1.20  %Foreground sorts:
% 2.00/1.20  
% 2.00/1.20  
% 2.00/1.20  %Background operators:
% 2.00/1.20  
% 2.00/1.20  
% 2.00/1.20  %Foreground operators:
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.00/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.20  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.00/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.20  
% 2.00/1.22  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.00/1.22  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.00/1.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.00/1.22  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.00/1.22  tff(f_63, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 2.00/1.22  tff(f_59, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 2.00/1.22  tff(f_75, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 2.00/1.22  tff(f_77, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.00/1.22  tff(f_80, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 2.00/1.22  tff(c_51, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.22  tff(c_12, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.22  tff(c_61, plain, (![B_36]: (k3_xboole_0(k1_xboole_0, B_36)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_51, c_12])).
% 2.00/1.22  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.22  tff(c_78, plain, (![B_37]: (k3_xboole_0(k1_xboole_0, B_37)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_51, c_12])).
% 2.00/1.22  tff(c_8, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.22  tff(c_83, plain, (![B_37, C_7]: (~r1_xboole_0(k1_xboole_0, B_37) | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_8])).
% 2.00/1.22  tff(c_90, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_83])).
% 2.00/1.22  tff(c_106, plain, (![B_41, A_42]: (r2_hidden(B_41, A_42) | k3_xboole_0(A_42, k1_tarski(B_41))!=k1_tarski(B_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.00/1.22  tff(c_113, plain, (![B_41]: (r2_hidden(B_41, k1_xboole_0) | k1_tarski(B_41)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_106])).
% 2.00/1.22  tff(c_114, plain, (![B_41]: (k1_tarski(B_41)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_90, c_113])).
% 2.00/1.22  tff(c_20, plain, (![A_15, B_16]: (k2_zfmisc_1(k1_tarski(A_15), k1_tarski(B_16))=k1_tarski(k4_tarski(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.22  tff(c_180, plain, (![A_56, B_57]: (k1_relat_1(k2_zfmisc_1(A_56, B_57))=A_56 | k1_xboole_0=B_57 | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.22  tff(c_189, plain, (![A_15, B_16]: (k1_relat_1(k1_tarski(k4_tarski(A_15, B_16)))=k1_tarski(A_15) | k1_tarski(B_16)=k1_xboole_0 | k1_tarski(A_15)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_180])).
% 2.00/1.22  tff(c_192, plain, (![A_15, B_16]: (k1_relat_1(k1_tarski(k4_tarski(A_15, B_16)))=k1_tarski(A_15))), inference(negUnitSimplification, [status(thm)], [c_114, c_114, c_189])).
% 2.00/1.22  tff(c_28, plain, (![A_21, B_22, C_23]: (k4_tarski(k4_tarski(A_21, B_22), C_23)=k3_mcart_1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.00/1.22  tff(c_193, plain, (![A_58, B_59]: (k1_relat_1(k1_tarski(k4_tarski(A_58, B_59)))=k1_tarski(A_58))), inference(negUnitSimplification, [status(thm)], [c_114, c_114, c_189])).
% 2.00/1.22  tff(c_202, plain, (![A_21, B_22, C_23]: (k1_relat_1(k1_tarski(k3_mcart_1(A_21, B_22, C_23)))=k1_tarski(k4_tarski(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_193])).
% 2.00/1.22  tff(c_30, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_2', '#skF_3', '#skF_4'))))!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.00/1.22  tff(c_273, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_2', '#skF_3')))!=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_30])).
% 2.00/1.22  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_273])).
% 2.00/1.22  tff(c_278, plain, (![B_67]: (~r1_xboole_0(k1_xboole_0, B_67))), inference(splitRight, [status(thm)], [c_83])).
% 2.00/1.22  tff(c_282, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_278])).
% 2.00/1.22  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_282])).
% 2.00/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  Inference rules
% 2.00/1.22  ----------------------
% 2.00/1.22  #Ref     : 0
% 2.00/1.22  #Sup     : 55
% 2.00/1.22  #Fact    : 0
% 2.00/1.22  #Define  : 0
% 2.00/1.22  #Split   : 1
% 2.00/1.22  #Chain   : 0
% 2.00/1.22  #Close   : 0
% 2.00/1.22  
% 2.00/1.22  Ordering : KBO
% 2.00/1.22  
% 2.00/1.22  Simplification rules
% 2.00/1.22  ----------------------
% 2.00/1.22  #Subsume      : 3
% 2.00/1.22  #Demod        : 15
% 2.00/1.22  #Tautology    : 36
% 2.00/1.22  #SimpNegUnit  : 5
% 2.00/1.22  #BackRed      : 1
% 2.00/1.22  
% 2.00/1.22  #Partial instantiations: 0
% 2.00/1.22  #Strategies tried      : 1
% 2.00/1.22  
% 2.00/1.22  Timing (in seconds)
% 2.00/1.22  ----------------------
% 2.00/1.22  Preprocessing        : 0.28
% 2.00/1.22  Parsing              : 0.15
% 2.00/1.22  CNF conversion       : 0.02
% 2.00/1.22  Main loop            : 0.17
% 2.00/1.22  Inferencing          : 0.07
% 2.00/1.22  Reduction            : 0.05
% 2.00/1.22  Demodulation         : 0.03
% 2.00/1.22  BG Simplification    : 0.01
% 2.00/1.22  Subsumption          : 0.02
% 2.00/1.22  Abstraction          : 0.01
% 2.00/1.22  MUC search           : 0.00
% 2.00/1.22  Cooper               : 0.00
% 2.00/1.22  Total                : 0.48
% 2.00/1.22  Index Insertion      : 0.00
% 2.00/1.22  Index Deletion       : 0.00
% 2.00/1.22  Index Matching       : 0.00
% 2.00/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
