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
% DateTime   : Thu Dec  3 09:59:05 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 101 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 182 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_85,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_30,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_53,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    ! [A_19] :
      ( v1_relat_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_96,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_30,B_31)),k1_relat_1(A_30))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_101,plain,(
    ! [B_31] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_31)),k1_xboole_0)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_96])).

tff(c_105,plain,(
    ! [B_32] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_32)),k1_xboole_0)
      | ~ v1_relat_1(B_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_101])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_73,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_124,plain,(
    ! [B_35] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_35)) = k1_xboole_0
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_105,c_82])).

tff(c_18,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_139,plain,(
    ! [B_35] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_35))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_18])).

tff(c_202,plain,(
    ! [B_40] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_40))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_139])).

tff(c_49,plain,(
    ! [B_20,A_21] :
      ( ~ v1_xboole_0(B_20)
      | B_20 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_226,plain,(
    ! [B_42] :
      ( k5_relat_1(k1_xboole_0,B_42) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_202,c_52])).

tff(c_230,plain,(
    ! [B_8] :
      ( k5_relat_1(k1_xboole_0,B_8) = k1_xboole_0
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_226])).

tff(c_244,plain,(
    ! [B_45] :
      ( k5_relat_1(k1_xboole_0,B_45) = k1_xboole_0
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_230])).

tff(c_253,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_244])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_253])).

tff(c_260,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_403,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_60,B_61)),k2_relat_1(B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_411,plain,(
    ! [A_60] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_60,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_403])).

tff(c_465,plain,(
    ! [A_63] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_63,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_411])).

tff(c_284,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_293,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_284])).

tff(c_536,plain,(
    ! [A_66] :
      ( k2_relat_1(k5_relat_1(A_66,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_465,c_293])).

tff(c_20,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_551,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_66,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_66,k1_xboole_0))
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_20])).

tff(c_567,plain,(
    ! [A_67] :
      ( ~ v1_relat_1(k5_relat_1(A_67,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_67,k1_xboole_0))
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_551])).

tff(c_584,plain,(
    ! [A_68] :
      ( k5_relat_1(A_68,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_68,k1_xboole_0))
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_567,c_52])).

tff(c_591,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_16,c_584])).

tff(c_597,plain,(
    ! [A_69] :
      ( k5_relat_1(A_69,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_591])).

tff(c_606,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_597])).

tff(c_613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.42  
% 2.44/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.42  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.44/1.42  
% 2.44/1.42  %Foreground sorts:
% 2.44/1.42  
% 2.44/1.42  
% 2.44/1.42  %Background operators:
% 2.44/1.42  
% 2.44/1.42  
% 2.44/1.42  %Foreground operators:
% 2.44/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.44/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.44/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.44/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.44/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.44/1.42  
% 2.44/1.44  tff(f_92, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.44/1.44  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.44/1.44  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.44/1.44  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.44/1.44  tff(f_85, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.44/1.44  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.44/1.44  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.44/1.44  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.44/1.44  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.44/1.44  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.44/1.44  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.44/1.44  tff(f_68, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.44/1.44  tff(c_30, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.44/1.44  tff(c_53, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 2.44/1.44  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.44/1.44  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.44/1.44  tff(c_44, plain, (![A_19]: (v1_relat_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.44/1.44  tff(c_48, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_44])).
% 2.44/1.44  tff(c_16, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.44/1.44  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.44/1.44  tff(c_96, plain, (![A_30, B_31]: (r1_tarski(k1_relat_1(k5_relat_1(A_30, B_31)), k1_relat_1(A_30)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.44/1.44  tff(c_101, plain, (![B_31]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_31)), k1_xboole_0) | ~v1_relat_1(B_31) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_96])).
% 2.44/1.44  tff(c_105, plain, (![B_32]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_32)), k1_xboole_0) | ~v1_relat_1(B_32))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_101])).
% 2.44/1.44  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.44/1.44  tff(c_73, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.44/1.44  tff(c_82, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_73])).
% 2.44/1.44  tff(c_124, plain, (![B_35]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_35))=k1_xboole_0 | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_105, c_82])).
% 2.44/1.44  tff(c_18, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.44/1.44  tff(c_139, plain, (![B_35]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_35)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_35)) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_124, c_18])).
% 2.44/1.44  tff(c_202, plain, (![B_40]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_40)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_40)) | ~v1_relat_1(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_139])).
% 2.44/1.44  tff(c_49, plain, (![B_20, A_21]: (~v1_xboole_0(B_20) | B_20=A_21 | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.44/1.44  tff(c_52, plain, (![A_21]: (k1_xboole_0=A_21 | ~v1_xboole_0(A_21))), inference(resolution, [status(thm)], [c_2, c_49])).
% 2.44/1.44  tff(c_226, plain, (![B_42]: (k5_relat_1(k1_xboole_0, B_42)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_42)) | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_202, c_52])).
% 2.44/1.44  tff(c_230, plain, (![B_8]: (k5_relat_1(k1_xboole_0, B_8)=k1_xboole_0 | ~v1_relat_1(B_8) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_226])).
% 2.44/1.44  tff(c_244, plain, (![B_45]: (k5_relat_1(k1_xboole_0, B_45)=k1_xboole_0 | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_230])).
% 2.44/1.44  tff(c_253, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_244])).
% 2.44/1.44  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_253])).
% 2.44/1.44  tff(c_260, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.44/1.44  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.44/1.44  tff(c_403, plain, (![A_60, B_61]: (r1_tarski(k2_relat_1(k5_relat_1(A_60, B_61)), k2_relat_1(B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.44/1.44  tff(c_411, plain, (![A_60]: (r1_tarski(k2_relat_1(k5_relat_1(A_60, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_60))), inference(superposition, [status(thm), theory('equality')], [c_26, c_403])).
% 2.44/1.44  tff(c_465, plain, (![A_63]: (r1_tarski(k2_relat_1(k5_relat_1(A_63, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_411])).
% 2.44/1.44  tff(c_284, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.44/1.44  tff(c_293, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_284])).
% 2.44/1.44  tff(c_536, plain, (![A_66]: (k2_relat_1(k5_relat_1(A_66, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_465, c_293])).
% 2.44/1.44  tff(c_20, plain, (![A_10]: (~v1_xboole_0(k2_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.44/1.44  tff(c_551, plain, (![A_66]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_66, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_66, k1_xboole_0)) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_536, c_20])).
% 2.44/1.44  tff(c_567, plain, (![A_67]: (~v1_relat_1(k5_relat_1(A_67, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_67, k1_xboole_0)) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_551])).
% 2.44/1.44  tff(c_584, plain, (![A_68]: (k5_relat_1(A_68, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_68, k1_xboole_0)) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_567, c_52])).
% 2.44/1.44  tff(c_591, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_16, c_584])).
% 2.44/1.44  tff(c_597, plain, (![A_69]: (k5_relat_1(A_69, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_591])).
% 2.44/1.44  tff(c_606, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_597])).
% 2.44/1.44  tff(c_613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_606])).
% 2.44/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.44  
% 2.44/1.44  Inference rules
% 2.44/1.44  ----------------------
% 2.44/1.44  #Ref     : 0
% 2.44/1.44  #Sup     : 123
% 2.44/1.44  #Fact    : 0
% 2.44/1.44  #Define  : 0
% 2.44/1.44  #Split   : 1
% 2.44/1.44  #Chain   : 0
% 2.44/1.44  #Close   : 0
% 2.44/1.44  
% 2.44/1.44  Ordering : KBO
% 2.44/1.44  
% 2.44/1.44  Simplification rules
% 2.44/1.44  ----------------------
% 2.44/1.44  #Subsume      : 9
% 2.44/1.44  #Demod        : 133
% 2.44/1.44  #Tautology    : 72
% 2.44/1.44  #SimpNegUnit  : 2
% 2.44/1.44  #BackRed      : 0
% 2.44/1.44  
% 2.44/1.44  #Partial instantiations: 0
% 2.44/1.44  #Strategies tried      : 1
% 2.44/1.44  
% 2.44/1.44  Timing (in seconds)
% 2.44/1.44  ----------------------
% 2.44/1.44  Preprocessing        : 0.28
% 2.44/1.44  Parsing              : 0.16
% 2.44/1.44  CNF conversion       : 0.02
% 2.44/1.44  Main loop            : 0.34
% 2.44/1.44  Inferencing          : 0.14
% 2.44/1.44  Reduction            : 0.09
% 2.44/1.44  Demodulation         : 0.06
% 2.44/1.44  BG Simplification    : 0.02
% 2.44/1.44  Subsumption          : 0.07
% 2.44/1.44  Abstraction          : 0.02
% 2.44/1.44  MUC search           : 0.00
% 2.44/1.44  Cooper               : 0.00
% 2.44/1.44  Total                : 0.65
% 2.44/1.44  Index Insertion      : 0.00
% 2.44/1.44  Index Deletion       : 0.00
% 2.44/1.44  Index Matching       : 0.00
% 2.44/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
