%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:46 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   62 (  89 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 158 expanded)
%              Number of equality atoms :   29 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_43,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_80,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_40,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_69,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_103,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_34])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_410,plain,(
    ! [B_61,A_62] :
      ( k3_xboole_0(k1_relat_1(B_61),A_62) = k1_relat_1(k7_relat_1(B_61,A_62))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_90,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_32)
      | r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_132,plain,(
    ! [A_41,B_42,A_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | r1_xboole_0(A_43,k3_xboole_0(A_41,B_42)) ) ),
    inference(resolution,[status(thm)],[c_90,c_10])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ r1_xboole_0(A_12,A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_141,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_132,c_16])).

tff(c_152,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_141])).

tff(c_429,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_152])).

tff(c_462,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_429])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_70,plain,(
    ! [A_25] :
      ( k1_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_77,plain,(
    ! [A_15,B_16] :
      ( k1_relat_1(k7_relat_1(A_15,B_16)) != k1_xboole_0
      | k7_relat_1(A_15,B_16) = k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_471,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_77])).

tff(c_479,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_471])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_479])).

tff(c_482,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_501,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_34])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_529,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),A_71)
      | r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_541,plain,(
    ! [A_75,B_76,B_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | r1_xboole_0(k3_xboole_0(A_75,B_76),B_77) ) ),
    inference(resolution,[status(thm)],[c_529,c_10])).

tff(c_564,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = k1_xboole_0
      | ~ r1_xboole_0(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_541,c_16])).

tff(c_573,plain,(
    ! [A_85] : k3_xboole_0(A_85,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_564])).

tff(c_581,plain,(
    ! [A_85,C_10] :
      ( ~ r1_xboole_0(A_85,k1_xboole_0)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_10])).

tff(c_588,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_581])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_681,plain,(
    ! [B_94,A_95] :
      ( k3_xboole_0(k1_relat_1(B_94),A_95) = k1_relat_1(k7_relat_1(B_94,A_95))
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1124,plain,(
    ! [B_120,A_121] :
      ( r2_hidden('#skF_2'(k1_relat_1(B_120),A_121),k1_relat_1(k7_relat_1(B_120,A_121)))
      | r1_xboole_0(k1_relat_1(B_120),A_121)
      | ~ v1_relat_1(B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_8])).

tff(c_1145,plain,
    ( r2_hidden('#skF_2'(k1_relat_1('#skF_4'),'#skF_3'),k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_1124])).

tff(c_1161,plain,
    ( r2_hidden('#skF_2'(k1_relat_1('#skF_4'),'#skF_3'),k1_xboole_0)
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24,c_1145])).

tff(c_1163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_588,c_1161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:12:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/2.00  
% 3.59/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/2.00  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.59/2.00  
% 3.59/2.00  %Foreground sorts:
% 3.59/2.00  
% 3.59/2.00  
% 3.59/2.00  %Background operators:
% 3.59/2.00  
% 3.59/2.00  
% 3.59/2.00  %Foreground operators:
% 3.59/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/2.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.59/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.59/2.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.59/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.59/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.59/2.00  tff('#skF_3', type, '#skF_3': $i).
% 3.59/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.59/2.00  tff('#skF_4', type, '#skF_4': $i).
% 3.59/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.59/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.59/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.59/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.59/2.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.59/2.00  
% 3.59/2.02  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 3.59/2.02  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.59/2.02  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.59/2.02  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.59/2.02  tff(f_71, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.59/2.02  tff(f_77, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.59/2.02  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.59/2.02  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.59/2.02  tff(f_80, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.59/2.02  tff(c_40, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.59/2.02  tff(c_69, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 3.59/2.02  tff(c_34, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.59/2.02  tff(c_103, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69, c_34])).
% 3.59/2.02  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.59/2.02  tff(c_410, plain, (![B_61, A_62]: (k3_xboole_0(k1_relat_1(B_61), A_62)=k1_relat_1(k7_relat_1(B_61, A_62)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.59/2.02  tff(c_90, plain, (![A_31, B_32]: (r2_hidden('#skF_1'(A_31, B_32), B_32) | r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.59/2.02  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.59/2.02  tff(c_132, plain, (![A_41, B_42, A_43]: (~r1_xboole_0(A_41, B_42) | r1_xboole_0(A_43, k3_xboole_0(A_41, B_42)))), inference(resolution, [status(thm)], [c_90, c_10])).
% 3.59/2.02  tff(c_16, plain, (![A_12]: (~r1_xboole_0(A_12, A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.59/2.02  tff(c_141, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_xboole_0(A_44, B_45))), inference(resolution, [status(thm)], [c_132, c_16])).
% 3.59/2.02  tff(c_152, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_141])).
% 3.59/2.02  tff(c_429, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_410, c_152])).
% 3.59/2.02  tff(c_462, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_429])).
% 3.59/2.02  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.59/2.02  tff(c_70, plain, (![A_25]: (k1_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.59/2.02  tff(c_77, plain, (![A_15, B_16]: (k1_relat_1(k7_relat_1(A_15, B_16))!=k1_xboole_0 | k7_relat_1(A_15, B_16)=k1_xboole_0 | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_20, c_70])).
% 3.59/2.02  tff(c_471, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_462, c_77])).
% 3.59/2.02  tff(c_479, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_471])).
% 3.59/2.02  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_479])).
% 3.59/2.02  tff(c_482, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.59/2.02  tff(c_501, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_482, c_34])).
% 3.59/2.02  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.59/2.02  tff(c_529, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), A_71) | r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.59/2.02  tff(c_541, plain, (![A_75, B_76, B_77]: (~r1_xboole_0(A_75, B_76) | r1_xboole_0(k3_xboole_0(A_75, B_76), B_77))), inference(resolution, [status(thm)], [c_529, c_10])).
% 3.59/2.02  tff(c_564, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=k1_xboole_0 | ~r1_xboole_0(A_83, B_84))), inference(resolution, [status(thm)], [c_541, c_16])).
% 3.59/2.02  tff(c_573, plain, (![A_85]: (k3_xboole_0(A_85, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_564])).
% 3.59/2.02  tff(c_581, plain, (![A_85, C_10]: (~r1_xboole_0(A_85, k1_xboole_0) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_573, c_10])).
% 3.59/2.02  tff(c_588, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_581])).
% 3.59/2.02  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.59/2.02  tff(c_681, plain, (![B_94, A_95]: (k3_xboole_0(k1_relat_1(B_94), A_95)=k1_relat_1(k7_relat_1(B_94, A_95)) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.59/2.02  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.59/2.02  tff(c_1124, plain, (![B_120, A_121]: (r2_hidden('#skF_2'(k1_relat_1(B_120), A_121), k1_relat_1(k7_relat_1(B_120, A_121))) | r1_xboole_0(k1_relat_1(B_120), A_121) | ~v1_relat_1(B_120))), inference(superposition, [status(thm), theory('equality')], [c_681, c_8])).
% 3.59/2.02  tff(c_1145, plain, (r2_hidden('#skF_2'(k1_relat_1('#skF_4'), '#skF_3'), k1_relat_1(k1_xboole_0)) | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_482, c_1124])).
% 3.59/2.02  tff(c_1161, plain, (r2_hidden('#skF_2'(k1_relat_1('#skF_4'), '#skF_3'), k1_xboole_0) | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24, c_1145])).
% 3.59/2.02  tff(c_1163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_501, c_588, c_1161])).
% 3.59/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/2.02  
% 3.59/2.02  Inference rules
% 3.59/2.02  ----------------------
% 3.59/2.02  #Ref     : 0
% 3.59/2.02  #Sup     : 250
% 3.59/2.02  #Fact    : 0
% 3.59/2.02  #Define  : 0
% 3.59/2.02  #Split   : 4
% 3.59/2.02  #Chain   : 0
% 3.59/2.02  #Close   : 0
% 3.59/2.02  
% 3.59/2.02  Ordering : KBO
% 3.59/2.02  
% 3.59/2.02  Simplification rules
% 3.59/2.02  ----------------------
% 3.59/2.02  #Subsume      : 33
% 3.59/2.02  #Demod        : 186
% 3.59/2.02  #Tautology    : 152
% 3.59/2.02  #SimpNegUnit  : 14
% 3.59/2.02  #BackRed      : 1
% 3.59/2.02  
% 3.59/2.02  #Partial instantiations: 0
% 3.59/2.02  #Strategies tried      : 1
% 3.59/2.02  
% 3.59/2.02  Timing (in seconds)
% 3.59/2.02  ----------------------
% 3.59/2.03  Preprocessing        : 0.50
% 3.59/2.03  Parsing              : 0.26
% 3.59/2.03  CNF conversion       : 0.03
% 3.59/2.03  Main loop            : 0.58
% 3.59/2.03  Inferencing          : 0.22
% 3.59/2.03  Reduction            : 0.18
% 3.59/2.03  Demodulation         : 0.13
% 3.59/2.03  BG Simplification    : 0.03
% 3.59/2.03  Subsumption          : 0.11
% 3.59/2.03  Abstraction          : 0.03
% 3.59/2.03  MUC search           : 0.00
% 3.59/2.03  Cooper               : 0.00
% 3.59/2.03  Total                : 1.13
% 3.59/2.03  Index Insertion      : 0.00
% 3.59/2.03  Index Deletion       : 0.00
% 3.59/2.03  Index Matching       : 0.00
% 3.59/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
