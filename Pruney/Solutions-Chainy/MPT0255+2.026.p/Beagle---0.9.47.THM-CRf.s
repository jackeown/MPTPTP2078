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
% DateTime   : Thu Dec  3 09:51:42 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 155 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 ( 184 expanded)
%              Number of equality atoms :   20 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_54,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_35,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_2'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ v1_xboole_0(k2_xboole_0(B_8,A_7))
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_10])).

tff(c_92,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_88])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_97,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_14,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_101,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_14])).

tff(c_98,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_35])).

tff(c_133,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_157,plain,(
    ! [B_44,A_45] : k3_tarski(k2_tarski(B_44,A_45)) = k2_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_133])).

tff(c_26,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_180,plain,(
    ! [B_46,A_47] : k2_xboole_0(B_46,A_47) = k2_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_26])).

tff(c_222,plain,(
    k2_xboole_0('#skF_4',k2_tarski('#skF_3','#skF_2')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_180])).

tff(c_234,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_tarski('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_10])).

tff(c_238,plain,(
    v1_xboole_0(k2_tarski('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_234])).

tff(c_100,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_4])).

tff(c_243,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_238,c_100])).

tff(c_312,plain,(
    ! [A_52,C_53,B_54] :
      ( r2_hidden(A_52,C_53)
      | ~ r1_tarski(k2_tarski(A_52,B_54),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_315,plain,(
    ! [C_53] :
      ( r2_hidden('#skF_3',C_53)
      | ~ r1_tarski('#skF_4',C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_312])).

tff(c_323,plain,(
    ! [C_53] : r2_hidden('#skF_3',C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_315])).

tff(c_16,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_16])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    ! [A_9] : k3_xboole_0(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_97,c_12])).

tff(c_347,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,k3_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_356,plain,(
    ! [A_9,C_60] :
      ( ~ r1_xboole_0(A_9,'#skF_4')
      | ~ r2_hidden(C_60,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_347])).

tff(c_370,plain,(
    ! [C_64] : ~ r2_hidden(C_64,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_356])).

tff(c_378,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_323,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:44:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.95/1.23  
% 1.95/1.23  %Foreground sorts:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Background operators:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Foreground operators:
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.95/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.23  
% 2.17/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.17/1.24  tff(f_58, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.17/1.24  tff(f_76, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.17/1.24  tff(f_50, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.17/1.24  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.17/1.24  tff(f_54, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.17/1.24  tff(f_66, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.17/1.24  tff(f_72, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.17/1.24  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.17/1.24  tff(f_52, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.17/1.24  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.17/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.17/1.24  tff(c_18, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.24  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.24  tff(c_35, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_2'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_34])).
% 2.17/1.24  tff(c_10, plain, (![B_8, A_7]: (~v1_xboole_0(k2_xboole_0(B_8, A_7)) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.24  tff(c_88, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_35, c_10])).
% 2.17/1.24  tff(c_92, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_88])).
% 2.17/1.24  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.17/1.24  tff(c_97, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_92, c_4])).
% 2.17/1.24  tff(c_14, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.24  tff(c_101, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_14])).
% 2.17/1.24  tff(c_98, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_35])).
% 2.17/1.24  tff(c_133, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.24  tff(c_157, plain, (![B_44, A_45]: (k3_tarski(k2_tarski(B_44, A_45))=k2_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_18, c_133])).
% 2.17/1.24  tff(c_26, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.24  tff(c_180, plain, (![B_46, A_47]: (k2_xboole_0(B_46, A_47)=k2_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_157, c_26])).
% 2.17/1.24  tff(c_222, plain, (k2_xboole_0('#skF_4', k2_tarski('#skF_3', '#skF_2'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_98, c_180])).
% 2.17/1.24  tff(c_234, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0(k2_tarski('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_10])).
% 2.17/1.24  tff(c_238, plain, (v1_xboole_0(k2_tarski('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_234])).
% 2.17/1.24  tff(c_100, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_4])).
% 2.17/1.24  tff(c_243, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_238, c_100])).
% 2.17/1.24  tff(c_312, plain, (![A_52, C_53, B_54]: (r2_hidden(A_52, C_53) | ~r1_tarski(k2_tarski(A_52, B_54), C_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.17/1.24  tff(c_315, plain, (![C_53]: (r2_hidden('#skF_3', C_53) | ~r1_tarski('#skF_4', C_53))), inference(superposition, [status(thm), theory('equality')], [c_243, c_312])).
% 2.17/1.24  tff(c_323, plain, (![C_53]: (r2_hidden('#skF_3', C_53))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_315])).
% 2.17/1.24  tff(c_16, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.24  tff(c_102, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_16])).
% 2.17/1.24  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.24  tff(c_99, plain, (![A_9]: (k3_xboole_0(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_97, c_12])).
% 2.17/1.24  tff(c_347, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.24  tff(c_356, plain, (![A_9, C_60]: (~r1_xboole_0(A_9, '#skF_4') | ~r2_hidden(C_60, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_347])).
% 2.17/1.24  tff(c_370, plain, (![C_64]: (~r2_hidden(C_64, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_356])).
% 2.17/1.24  tff(c_378, plain, $false, inference(resolution, [status(thm)], [c_323, c_370])).
% 2.17/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  Inference rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Ref     : 0
% 2.17/1.24  #Sup     : 88
% 2.17/1.24  #Fact    : 0
% 2.17/1.24  #Define  : 0
% 2.17/1.24  #Split   : 1
% 2.17/1.24  #Chain   : 0
% 2.17/1.24  #Close   : 0
% 2.17/1.24  
% 2.17/1.24  Ordering : KBO
% 2.17/1.24  
% 2.17/1.24  Simplification rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Subsume      : 9
% 2.17/1.24  #Demod        : 38
% 2.17/1.24  #Tautology    : 62
% 2.17/1.24  #SimpNegUnit  : 0
% 2.17/1.24  #BackRed      : 9
% 2.17/1.24  
% 2.17/1.24  #Partial instantiations: 0
% 2.17/1.24  #Strategies tried      : 1
% 2.17/1.24  
% 2.17/1.24  Timing (in seconds)
% 2.17/1.24  ----------------------
% 2.17/1.24  Preprocessing        : 0.29
% 2.17/1.24  Parsing              : 0.16
% 2.17/1.24  CNF conversion       : 0.02
% 2.17/1.24  Main loop            : 0.20
% 2.17/1.24  Inferencing          : 0.07
% 2.17/1.24  Reduction            : 0.07
% 2.17/1.24  Demodulation         : 0.06
% 2.17/1.24  BG Simplification    : 0.01
% 2.17/1.24  Subsumption          : 0.04
% 2.17/1.25  Abstraction          : 0.01
% 2.17/1.25  MUC search           : 0.00
% 2.17/1.25  Cooper               : 0.00
% 2.17/1.25  Total                : 0.52
% 2.17/1.25  Index Insertion      : 0.00
% 2.17/1.25  Index Deletion       : 0.00
% 2.17/1.25  Index Matching       : 0.00
% 2.17/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
