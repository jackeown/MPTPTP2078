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
% DateTime   : Thu Dec  3 10:01:31 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   49 (  57 expanded)
%              Number of leaves         :   29 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  67 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_26,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_312,plain,(
    ! [A_86,B_87,C_88] :
      ( r2_hidden('#skF_1'(A_86,B_87,C_88),A_86)
      | r2_hidden('#skF_2'(A_86,B_87,C_88),C_88)
      | k4_xboole_0(A_86,B_87) = C_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,(
    ! [A_12,C_36] :
      ( ~ r1_xboole_0(A_12,k1_xboole_0)
      | ~ r2_hidden(C_36,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_113])).

tff(c_118,plain,(
    ! [C_36] : ~ r2_hidden(C_36,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_116])).

tff(c_360,plain,(
    ! [B_87,C_88] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_87,C_88),C_88)
      | k4_xboole_0(k1_xboole_0,B_87) = C_88 ) ),
    inference(resolution,[status(thm)],[c_312,c_118])).

tff(c_441,plain,(
    ! [B_89,C_90] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_89,C_90),C_90)
      | k1_xboole_0 = C_90 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_360])).

tff(c_61,plain,(
    ! [B_28] : k2_zfmisc_1(k1_xboole_0,B_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_36])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_179,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden('#skF_4'(A_54,B_55,C_56),k2_relat_1(C_56))
      | ~ r2_hidden(A_54,k10_relat_1(C_56,B_55))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_182,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_4'(A_54,B_55,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_54,k10_relat_1(k1_xboole_0,B_55))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_179])).

tff(c_184,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_4'(A_54,B_55,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_54,k10_relat_1(k1_xboole_0,B_55)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_182])).

tff(c_185,plain,(
    ! [A_54,B_55] : ~ r2_hidden(A_54,k10_relat_1(k1_xboole_0,B_55)) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_184])).

tff(c_501,plain,(
    ! [B_55] : k10_relat_1(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_441,c_185])).

tff(c_50,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:28:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2
% 2.17/1.29  
% 2.17/1.29  %Foreground sorts:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Background operators:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Foreground operators:
% 2.17/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.17/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.17/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.17/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.29  
% 2.17/1.30  tff(f_53, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.17/1.30  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.17/1.30  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.17/1.30  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.17/1.30  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.17/1.30  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.17/1.30  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.30  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.17/1.30  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.17/1.30  tff(f_80, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.17/1.30  tff(c_26, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.30  tff(c_312, plain, (![A_86, B_87, C_88]: (r2_hidden('#skF_1'(A_86, B_87, C_88), A_86) | r2_hidden('#skF_2'(A_86, B_87, C_88), C_88) | k4_xboole_0(A_86, B_87)=C_88)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.30  tff(c_28, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.17/1.30  tff(c_24, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.30  tff(c_113, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.30  tff(c_116, plain, (![A_12, C_36]: (~r1_xboole_0(A_12, k1_xboole_0) | ~r2_hidden(C_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_113])).
% 2.17/1.30  tff(c_118, plain, (![C_36]: (~r2_hidden(C_36, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_116])).
% 2.17/1.30  tff(c_360, plain, (![B_87, C_88]: (r2_hidden('#skF_2'(k1_xboole_0, B_87, C_88), C_88) | k4_xboole_0(k1_xboole_0, B_87)=C_88)), inference(resolution, [status(thm)], [c_312, c_118])).
% 2.17/1.30  tff(c_441, plain, (![B_89, C_90]: (r2_hidden('#skF_2'(k1_xboole_0, B_89, C_90), C_90) | k1_xboole_0=C_90)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_360])).
% 2.17/1.30  tff(c_61, plain, (![B_28]: (k2_zfmisc_1(k1_xboole_0, B_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.30  tff(c_36, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.17/1.30  tff(c_65, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_36])).
% 2.17/1.30  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.17/1.30  tff(c_179, plain, (![A_54, B_55, C_56]: (r2_hidden('#skF_4'(A_54, B_55, C_56), k2_relat_1(C_56)) | ~r2_hidden(A_54, k10_relat_1(C_56, B_55)) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.17/1.30  tff(c_182, plain, (![A_54, B_55]: (r2_hidden('#skF_4'(A_54, B_55, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_54, k10_relat_1(k1_xboole_0, B_55)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_179])).
% 2.17/1.30  tff(c_184, plain, (![A_54, B_55]: (r2_hidden('#skF_4'(A_54, B_55, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_54, k10_relat_1(k1_xboole_0, B_55)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_182])).
% 2.17/1.30  tff(c_185, plain, (![A_54, B_55]: (~r2_hidden(A_54, k10_relat_1(k1_xboole_0, B_55)))), inference(negUnitSimplification, [status(thm)], [c_118, c_184])).
% 2.17/1.30  tff(c_501, plain, (![B_55]: (k10_relat_1(k1_xboole_0, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_441, c_185])).
% 2.17/1.30  tff(c_50, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.17/1.30  tff(c_516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_501, c_50])).
% 2.17/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  Inference rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Ref     : 0
% 2.17/1.30  #Sup     : 93
% 2.17/1.30  #Fact    : 0
% 2.17/1.30  #Define  : 0
% 2.17/1.30  #Split   : 0
% 2.17/1.30  #Chain   : 0
% 2.17/1.30  #Close   : 0
% 2.17/1.30  
% 2.17/1.30  Ordering : KBO
% 2.17/1.30  
% 2.17/1.30  Simplification rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Subsume      : 10
% 2.17/1.30  #Demod        : 18
% 2.17/1.30  #Tautology    : 22
% 2.17/1.30  #SimpNegUnit  : 4
% 2.17/1.30  #BackRed      : 5
% 2.17/1.30  
% 2.17/1.30  #Partial instantiations: 0
% 2.17/1.30  #Strategies tried      : 1
% 2.17/1.30  
% 2.17/1.30  Timing (in seconds)
% 2.17/1.30  ----------------------
% 2.17/1.30  Preprocessing        : 0.29
% 2.17/1.30  Parsing              : 0.16
% 2.17/1.30  CNF conversion       : 0.02
% 2.17/1.30  Main loop            : 0.26
% 2.17/1.30  Inferencing          : 0.10
% 2.17/1.30  Reduction            : 0.06
% 2.17/1.30  Demodulation         : 0.04
% 2.17/1.30  BG Simplification    : 0.02
% 2.17/1.30  Subsumption          : 0.06
% 2.17/1.30  Abstraction          : 0.01
% 2.17/1.30  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.57
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
