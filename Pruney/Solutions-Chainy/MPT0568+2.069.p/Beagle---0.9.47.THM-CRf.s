%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:29 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   50 (  71 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  91 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_86,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_47,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_24,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_3'(A_15),A_15)
      | v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ r1_xboole_0(A_48,B_49)
      | ~ r2_hidden(C_50,k3_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ! [A_13,C_50] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_50,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_65])).

tff(c_81,plain,(
    ! [C_51] : ~ r2_hidden(C_51,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_76])).

tff(c_92,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_110,plain,(
    ! [A_56] :
      ( k10_relat_1(A_56,k2_relat_1(A_56)) = k1_relat_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_119,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_110])).

tff(c_123,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_32,c_119])).

tff(c_99,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_76])).

tff(c_124,plain,(
    ! [B_57] : r1_xboole_0(k1_xboole_0,B_57) ),
    inference(resolution,[status(thm)],[c_99,c_80])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    ! [B_57] : k3_xboole_0(k1_xboole_0,B_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_343,plain,(
    ! [B_76,A_77] :
      ( k10_relat_1(B_76,k3_xboole_0(k2_relat_1(B_76),A_77)) = k10_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_360,plain,(
    ! [A_77] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_77)) = k10_relat_1(k1_xboole_0,A_77)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_343])).

tff(c_365,plain,(
    ! [A_77] : k10_relat_1(k1_xboole_0,A_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_123,c_128,c_360])).

tff(c_34,plain,(
    k10_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:42:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.29  
% 2.00/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.29  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.00/1.29  
% 2.00/1.29  %Foreground sorts:
% 2.00/1.29  
% 2.00/1.29  
% 2.00/1.29  %Background operators:
% 2.00/1.29  
% 2.00/1.29  
% 2.00/1.29  %Foreground operators:
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.00/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.00/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.00/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.29  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.00/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.00/1.29  
% 2.00/1.30  tff(f_75, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.00/1.30  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.00/1.30  tff(f_63, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.00/1.30  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.00/1.30  tff(f_86, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.00/1.30  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.00/1.30  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.00/1.30  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.00/1.30  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.00/1.30  tff(f_89, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.00/1.30  tff(c_24, plain, (![A_15]: (r2_hidden('#skF_3'(A_15), A_15) | v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.30  tff(c_18, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.30  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.00/1.30  tff(c_65, plain, (![A_48, B_49, C_50]: (~r1_xboole_0(A_48, B_49) | ~r2_hidden(C_50, k3_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.30  tff(c_76, plain, (![A_13, C_50]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_65])).
% 2.00/1.30  tff(c_81, plain, (![C_51]: (~r2_hidden(C_51, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_76])).
% 2.00/1.30  tff(c_92, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_81])).
% 2.00/1.30  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.00/1.30  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.00/1.30  tff(c_110, plain, (![A_56]: (k10_relat_1(A_56, k2_relat_1(A_56))=k1_relat_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.00/1.30  tff(c_119, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_110])).
% 2.00/1.30  tff(c_123, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92, c_32, c_119])).
% 2.00/1.30  tff(c_99, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.30  tff(c_80, plain, (![C_50]: (~r2_hidden(C_50, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_76])).
% 2.00/1.30  tff(c_124, plain, (![B_57]: (r1_xboole_0(k1_xboole_0, B_57))), inference(resolution, [status(thm)], [c_99, c_80])).
% 2.00/1.30  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.30  tff(c_128, plain, (![B_57]: (k3_xboole_0(k1_xboole_0, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_124, c_2])).
% 2.00/1.30  tff(c_343, plain, (![B_76, A_77]: (k10_relat_1(B_76, k3_xboole_0(k2_relat_1(B_76), A_77))=k10_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.00/1.30  tff(c_360, plain, (![A_77]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_77))=k10_relat_1(k1_xboole_0, A_77) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_343])).
% 2.00/1.30  tff(c_365, plain, (![A_77]: (k10_relat_1(k1_xboole_0, A_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_123, c_128, c_360])).
% 2.00/1.30  tff(c_34, plain, (k10_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.00/1.30  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_365, c_34])).
% 2.00/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  Inference rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Ref     : 0
% 2.00/1.30  #Sup     : 77
% 2.00/1.30  #Fact    : 0
% 2.00/1.30  #Define  : 0
% 2.00/1.30  #Split   : 0
% 2.00/1.30  #Chain   : 0
% 2.00/1.30  #Close   : 0
% 2.00/1.30  
% 2.00/1.30  Ordering : KBO
% 2.00/1.30  
% 2.00/1.30  Simplification rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Subsume      : 9
% 2.00/1.30  #Demod        : 45
% 2.00/1.30  #Tautology    : 56
% 2.00/1.30  #SimpNegUnit  : 4
% 2.00/1.30  #BackRed      : 1
% 2.00/1.30  
% 2.00/1.30  #Partial instantiations: 0
% 2.00/1.30  #Strategies tried      : 1
% 2.00/1.30  
% 2.00/1.30  Timing (in seconds)
% 2.00/1.30  ----------------------
% 2.00/1.31  Preprocessing        : 0.28
% 2.00/1.31  Parsing              : 0.16
% 2.00/1.31  CNF conversion       : 0.02
% 2.00/1.31  Main loop            : 0.20
% 2.00/1.31  Inferencing          : 0.08
% 2.00/1.31  Reduction            : 0.06
% 2.00/1.31  Demodulation         : 0.04
% 2.00/1.31  BG Simplification    : 0.01
% 2.00/1.31  Subsumption          : 0.03
% 2.00/1.31  Abstraction          : 0.01
% 2.00/1.31  MUC search           : 0.00
% 2.00/1.31  Cooper               : 0.00
% 2.00/1.31  Total                : 0.51
% 2.00/1.31  Index Insertion      : 0.00
% 2.00/1.31  Index Deletion       : 0.00
% 2.00/1.31  Index Matching       : 0.00
% 2.00/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
