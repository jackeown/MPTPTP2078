%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:40 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 120 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 244 expanded)
%              Number of equality atoms :   25 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).

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

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_47,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_55,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47,c_26])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    r1_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_88,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,(
    ! [C_37] :
      ( ~ r1_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_37,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_88])).

tff(c_104,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_99])).

tff(c_130,plain,(
    ! [A_43] : r1_xboole_0(A_43,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_104])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_43] : k3_xboole_0(A_43,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_2])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_441,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(A_71,B_72)),k3_xboole_0(k2_relat_1(A_71),k2_relat_1(B_72)))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_459,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_441])).

tff(c_465,plain,(
    r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_459])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_420,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_xboole_0 = A_65
      | ~ r1_xboole_0(B_66,C_67)
      | ~ r1_tarski(A_65,C_67)
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_584,plain,(
    ! [A_80,B_81,A_82] :
      ( k1_xboole_0 = A_80
      | ~ r1_tarski(A_80,B_81)
      | ~ r1_tarski(A_80,A_82)
      | k3_xboole_0(A_82,B_81) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_420])).

tff(c_592,plain,(
    ! [A_82] :
      ( k2_relat_1(k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0
      | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),A_82)
      | k3_xboole_0(A_82,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_465,c_584])).

tff(c_602,plain,(
    ! [A_82] :
      ( k2_relat_1(k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0
      | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_592])).

tff(c_604,plain,(
    ! [A_82] : ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),A_82) ),
    inference(splitLeft,[status(thm)],[c_602])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_604,c_465])).

tff(c_607,plain,(
    k2_relat_1(k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_602])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_71,plain,(
    ! [A_30] :
      ( k2_relat_1(A_30) != k1_xboole_0
      | k1_xboole_0 = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_81,plain,(
    ! [A_16,B_17] :
      ( k2_relat_1(k3_xboole_0(A_16,B_17)) != k1_xboole_0
      | k3_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_612,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_81])).

tff(c_632,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_612])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.44  
% 2.42/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.42/1.44  
% 2.42/1.44  %Foreground sorts:
% 2.42/1.44  
% 2.42/1.44  
% 2.42/1.44  %Background operators:
% 2.42/1.44  
% 2.42/1.44  
% 2.42/1.44  %Foreground operators:
% 2.42/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.42/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.42/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.42/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.42/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.44  
% 2.69/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.69/1.45  tff(f_98, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t215_relat_1)).
% 2.69/1.45  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.69/1.45  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.69/1.45  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 2.69/1.45  tff(f_69, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.69/1.45  tff(f_73, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.69/1.45  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.69/1.45  tff(c_47, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.45  tff(c_26, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.69/1.45  tff(c_55, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_47, c_26])).
% 2.69/1.45  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.69/1.45  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.69/1.45  tff(c_28, plain, (r1_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.69/1.45  tff(c_34, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.45  tff(c_38, plain, (k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_34])).
% 2.69/1.45  tff(c_88, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.69/1.45  tff(c_99, plain, (![C_37]: (~r1_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')) | ~r2_hidden(C_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_88])).
% 2.69/1.45  tff(c_104, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_99])).
% 2.69/1.45  tff(c_130, plain, (![A_43]: (r1_xboole_0(A_43, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_104])).
% 2.69/1.45  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.45  tff(c_137, plain, (![A_43]: (k3_xboole_0(A_43, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_2])).
% 2.69/1.45  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.69/1.45  tff(c_441, plain, (![A_71, B_72]: (r1_tarski(k2_relat_1(k3_xboole_0(A_71, B_72)), k3_xboole_0(k2_relat_1(A_71), k2_relat_1(B_72))) | ~v1_relat_1(B_72) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.69/1.45  tff(c_459, plain, (r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k1_xboole_0) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_441])).
% 2.69/1.45  tff(c_465, plain, (r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_459])).
% 2.69/1.45  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.45  tff(c_420, plain, (![A_65, B_66, C_67]: (k1_xboole_0=A_65 | ~r1_xboole_0(B_66, C_67) | ~r1_tarski(A_65, C_67) | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.45  tff(c_584, plain, (![A_80, B_81, A_82]: (k1_xboole_0=A_80 | ~r1_tarski(A_80, B_81) | ~r1_tarski(A_80, A_82) | k3_xboole_0(A_82, B_81)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_420])).
% 2.69/1.45  tff(c_592, plain, (![A_82]: (k2_relat_1(k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0 | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), A_82) | k3_xboole_0(A_82, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_465, c_584])).
% 2.69/1.45  tff(c_602, plain, (![A_82]: (k2_relat_1(k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0 | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), A_82))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_592])).
% 2.69/1.45  tff(c_604, plain, (![A_82]: (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), A_82))), inference(splitLeft, [status(thm)], [c_602])).
% 2.69/1.45  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_604, c_465])).
% 2.69/1.45  tff(c_607, plain, (k2_relat_1(k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_602])).
% 2.69/1.45  tff(c_18, plain, (![A_16, B_17]: (v1_relat_1(k3_xboole_0(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.69/1.45  tff(c_71, plain, (![A_30]: (k2_relat_1(A_30)!=k1_xboole_0 | k1_xboole_0=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.69/1.45  tff(c_81, plain, (![A_16, B_17]: (k2_relat_1(k3_xboole_0(A_16, B_17))!=k1_xboole_0 | k3_xboole_0(A_16, B_17)=k1_xboole_0 | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_18, c_71])).
% 2.69/1.45  tff(c_612, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_607, c_81])).
% 2.69/1.45  tff(c_632, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_612])).
% 2.69/1.45  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_632])).
% 2.69/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.45  
% 2.69/1.45  Inference rules
% 2.69/1.45  ----------------------
% 2.69/1.45  #Ref     : 0
% 2.69/1.45  #Sup     : 141
% 2.69/1.45  #Fact    : 0
% 2.69/1.45  #Define  : 0
% 2.69/1.45  #Split   : 7
% 2.69/1.45  #Chain   : 0
% 2.69/1.45  #Close   : 0
% 2.69/1.45  
% 2.69/1.45  Ordering : KBO
% 2.69/1.45  
% 2.69/1.45  Simplification rules
% 2.69/1.45  ----------------------
% 2.69/1.45  #Subsume      : 26
% 2.69/1.45  #Demod        : 74
% 2.69/1.45  #Tautology    : 66
% 2.69/1.45  #SimpNegUnit  : 11
% 2.69/1.45  #BackRed      : 4
% 2.69/1.45  
% 2.69/1.45  #Partial instantiations: 0
% 2.69/1.45  #Strategies tried      : 1
% 2.69/1.45  
% 2.69/1.45  Timing (in seconds)
% 2.69/1.45  ----------------------
% 2.69/1.46  Preprocessing        : 0.29
% 2.69/1.46  Parsing              : 0.17
% 2.69/1.46  CNF conversion       : 0.02
% 2.69/1.46  Main loop            : 0.31
% 2.69/1.46  Inferencing          : 0.12
% 2.69/1.46  Reduction            : 0.09
% 2.69/1.46  Demodulation         : 0.06
% 2.69/1.46  BG Simplification    : 0.01
% 2.69/1.46  Subsumption          : 0.06
% 2.69/1.46  Abstraction          : 0.01
% 2.69/1.46  MUC search           : 0.00
% 2.69/1.46  Cooper               : 0.00
% 2.69/1.46  Total                : 0.63
% 2.69/1.46  Index Insertion      : 0.00
% 2.69/1.46  Index Deletion       : 0.00
% 2.69/1.46  Index Matching       : 0.00
% 2.69/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
