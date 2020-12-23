%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:12 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 160 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_28,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_47,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_47])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_78,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_28,B_29)),k1_relat_1(A_28))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    ! [B_29] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_29)),k1_xboole_0)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_78])).

tff(c_84,plain,(
    ! [B_30] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_30)),k1_xboole_0)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_81])).

tff(c_8,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    ! [B_23,A_24] :
      ( ~ r1_xboole_0(B_23,A_24)
      | ~ r1_tarski(B_23,A_24)
      | v1_xboole_0(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,(
    ! [A_3] :
      ( ~ r1_tarski(A_3,k1_xboole_0)
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_89,plain,(
    ! [B_31] :
      ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_31)))
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_84,c_69])).

tff(c_16,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_179,plain,(
    ! [B_38] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_38))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_89,c_16])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_419,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_179,c_4])).

tff(c_426,plain,(
    ! [B_8] :
      ( k5_relat_1(k1_xboole_0,B_8) = k1_xboole_0
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_419])).

tff(c_432,plain,(
    ! [B_45] :
      ( k5_relat_1(k1_xboole_0,B_45) = k1_xboole_0
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_426])).

tff(c_444,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_432])).

tff(c_452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_444])).

tff(c_453,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_500,plain,(
    ! [B_55,A_56] :
      ( k2_relat_1(k5_relat_1(B_55,A_56)) = k2_relat_1(A_56)
      | ~ r1_tarski(k1_relat_1(A_56),k2_relat_1(B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_503,plain,(
    ! [B_55] :
      ( k2_relat_1(k5_relat_1(B_55,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_500])).

tff(c_511,plain,(
    ! [B_57] :
      ( k2_relat_1(k5_relat_1(B_57,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_6,c_24,c_503])).

tff(c_18,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_520,plain,(
    ! [B_57] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_57,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_57,k1_xboole_0))
      | ~ v1_relat_1(B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_18])).

tff(c_728,plain,(
    ! [B_64] :
      ( ~ v1_relat_1(k5_relat_1(B_64,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_64,k1_xboole_0))
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_520])).

tff(c_767,plain,(
    ! [B_66] :
      ( k5_relat_1(B_66,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_66,k1_xboole_0))
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_728,c_4])).

tff(c_774,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_767])).

tff(c_780,plain,(
    ! [A_67] :
      ( k5_relat_1(A_67,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_774])).

tff(c_792,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_780])).

tff(c_800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.37  
% 2.65/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.37  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.65/1.37  
% 2.65/1.37  %Foreground sorts:
% 2.65/1.37  
% 2.65/1.37  
% 2.65/1.37  %Background operators:
% 2.65/1.37  
% 2.65/1.37  
% 2.65/1.37  %Foreground operators:
% 2.65/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.65/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.65/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.37  
% 2.65/1.38  tff(f_94, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.65/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.65/1.38  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.65/1.38  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.65/1.38  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.65/1.38  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.65/1.38  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.65/1.38  tff(f_42, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.65/1.38  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.65/1.38  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.65/1.38  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.65/1.38  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.65/1.38  tff(f_68, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.65/1.38  tff(c_28, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.65/1.38  tff(c_52, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 2.65/1.38  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.65/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.65/1.38  tff(c_47, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.65/1.38  tff(c_51, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_47])).
% 2.65/1.38  tff(c_14, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.65/1.38  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.38  tff(c_78, plain, (![A_28, B_29]: (r1_tarski(k1_relat_1(k5_relat_1(A_28, B_29)), k1_relat_1(A_28)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.38  tff(c_81, plain, (![B_29]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_29)), k1_xboole_0) | ~v1_relat_1(B_29) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_78])).
% 2.65/1.38  tff(c_84, plain, (![B_30]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_30)), k1_xboole_0) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_81])).
% 2.65/1.38  tff(c_8, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.65/1.38  tff(c_65, plain, (![B_23, A_24]: (~r1_xboole_0(B_23, A_24) | ~r1_tarski(B_23, A_24) | v1_xboole_0(B_23))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.65/1.38  tff(c_69, plain, (![A_3]: (~r1_tarski(A_3, k1_xboole_0) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_8, c_65])).
% 2.65/1.38  tff(c_89, plain, (![B_31]: (v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_31))) | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_84, c_69])).
% 2.65/1.38  tff(c_16, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.65/1.38  tff(c_179, plain, (![B_38]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_38)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_38)) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_89, c_16])).
% 2.65/1.38  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.65/1.38  tff(c_419, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_44)) | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_179, c_4])).
% 2.65/1.38  tff(c_426, plain, (![B_8]: (k5_relat_1(k1_xboole_0, B_8)=k1_xboole_0 | ~v1_relat_1(B_8) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_419])).
% 2.65/1.38  tff(c_432, plain, (![B_45]: (k5_relat_1(k1_xboole_0, B_45)=k1_xboole_0 | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_426])).
% 2.65/1.38  tff(c_444, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_432])).
% 2.65/1.38  tff(c_452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_444])).
% 2.65/1.38  tff(c_453, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.65/1.38  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.38  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.38  tff(c_500, plain, (![B_55, A_56]: (k2_relat_1(k5_relat_1(B_55, A_56))=k2_relat_1(A_56) | ~r1_tarski(k1_relat_1(A_56), k2_relat_1(B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.65/1.38  tff(c_503, plain, (![B_55]: (k2_relat_1(k5_relat_1(B_55, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_500])).
% 2.65/1.38  tff(c_511, plain, (![B_57]: (k2_relat_1(k5_relat_1(B_57, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_57))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_6, c_24, c_503])).
% 2.65/1.38  tff(c_18, plain, (![A_10]: (~v1_xboole_0(k2_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.65/1.38  tff(c_520, plain, (![B_57]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_57, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_57, k1_xboole_0)) | ~v1_relat_1(B_57))), inference(superposition, [status(thm), theory('equality')], [c_511, c_18])).
% 2.65/1.38  tff(c_728, plain, (![B_64]: (~v1_relat_1(k5_relat_1(B_64, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_64, k1_xboole_0)) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_520])).
% 2.65/1.38  tff(c_767, plain, (![B_66]: (k5_relat_1(B_66, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_66, k1_xboole_0)) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_728, c_4])).
% 2.65/1.38  tff(c_774, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_14, c_767])).
% 2.65/1.38  tff(c_780, plain, (![A_67]: (k5_relat_1(A_67, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_774])).
% 2.65/1.38  tff(c_792, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_780])).
% 2.65/1.38  tff(c_800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_453, c_792])).
% 2.65/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.38  
% 2.65/1.38  Inference rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Ref     : 0
% 2.65/1.38  #Sup     : 161
% 2.65/1.38  #Fact    : 0
% 2.65/1.38  #Define  : 0
% 2.65/1.38  #Split   : 3
% 2.65/1.38  #Chain   : 0
% 2.65/1.38  #Close   : 0
% 2.65/1.38  
% 2.65/1.38  Ordering : KBO
% 2.65/1.38  
% 2.65/1.38  Simplification rules
% 2.65/1.38  ----------------------
% 2.65/1.38  #Subsume      : 5
% 2.65/1.38  #Demod        : 214
% 2.65/1.38  #Tautology    : 106
% 2.65/1.38  #SimpNegUnit  : 2
% 2.65/1.38  #BackRed      : 6
% 2.65/1.38  
% 2.65/1.38  #Partial instantiations: 0
% 2.65/1.38  #Strategies tried      : 1
% 2.65/1.38  
% 2.65/1.38  Timing (in seconds)
% 2.65/1.38  ----------------------
% 2.65/1.39  Preprocessing        : 0.30
% 2.65/1.39  Parsing              : 0.17
% 2.65/1.39  CNF conversion       : 0.02
% 2.65/1.39  Main loop            : 0.32
% 2.65/1.39  Inferencing          : 0.13
% 2.65/1.39  Reduction            : 0.09
% 2.65/1.39  Demodulation         : 0.06
% 2.65/1.39  BG Simplification    : 0.02
% 2.65/1.39  Subsumption          : 0.06
% 2.65/1.39  Abstraction          : 0.01
% 2.65/1.39  MUC search           : 0.00
% 2.65/1.39  Cooper               : 0.00
% 2.65/1.39  Total                : 0.65
% 2.65/1.39  Index Insertion      : 0.00
% 2.65/1.39  Index Deletion       : 0.00
% 2.65/1.39  Index Matching       : 0.00
% 2.65/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
