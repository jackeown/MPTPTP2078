%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:05 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 101 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 176 expanded)
%              Number of equality atoms :   33 (  51 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_85,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

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

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_32,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_57,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_21] :
      ( v1_relat_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k5_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_211,plain,(
    ! [A_44,B_45] :
      ( k1_relat_1(k5_relat_1(A_44,B_45)) = k1_relat_1(A_44)
      | ~ r1_tarski(k2_relat_1(A_44),k1_relat_1(B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_220,plain,(
    ! [B_45] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_45)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_211])).

tff(c_324,plain,(
    ! [B_49] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_49)) = k1_xboole_0
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12,c_30,c_220])).

tff(c_20,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k1_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_339,plain,(
    ! [B_49] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_49))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_20])).

tff(c_390,plain,(
    ! [B_52] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_52))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_339])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_407,plain,(
    ! [B_53] :
      ( k5_relat_1(k1_xboole_0,B_53) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_390,c_4])).

tff(c_414,plain,(
    ! [B_9] :
      ( k5_relat_1(k1_xboole_0,B_9) = k1_xboole_0
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_407])).

tff(c_431,plain,(
    ! [B_55] :
      ( k5_relat_1(k1_xboole_0,B_55) = k1_xboole_0
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_414])).

tff(c_443,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_431])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_443])).

tff(c_452,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_458,plain,(
    ! [A_56,B_57] :
      ( v1_xboole_0(k2_zfmisc_1(A_56,B_57))
      | ~ v1_xboole_0(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_468,plain,(
    ! [A_60,B_61] :
      ( k2_zfmisc_1(A_60,B_61) = k1_xboole_0
      | ~ v1_xboole_0(B_61) ) ),
    inference(resolution,[status(thm)],[c_458,c_4])).

tff(c_474,plain,(
    ! [A_60] : k2_zfmisc_1(A_60,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_468])).

tff(c_674,plain,(
    ! [B_79,A_80] :
      ( k2_relat_1(k5_relat_1(B_79,A_80)) = k2_relat_1(A_80)
      | ~ r1_tarski(k1_relat_1(A_80),k2_relat_1(B_79))
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_680,plain,(
    ! [B_79] :
      ( k2_relat_1(k5_relat_1(B_79,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_79))
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_674])).

tff(c_690,plain,(
    ! [B_81] :
      ( k2_relat_1(k5_relat_1(B_81,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12,c_28,c_680])).

tff(c_22,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_702,plain,(
    ! [B_81] :
      ( r1_tarski(k5_relat_1(B_81,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_81,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(B_81,k1_xboole_0))
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_22])).

tff(c_813,plain,(
    ! [B_87] :
      ( r1_tarski(k5_relat_1(B_87,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_87,k1_xboole_0))
      | ~ v1_relat_1(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_702])).

tff(c_504,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_513,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_504])).

tff(c_828,plain,(
    ! [B_88] :
      ( k5_relat_1(B_88,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_88,k1_xboole_0))
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_813,c_513])).

tff(c_835,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_828])).

tff(c_841,plain,(
    ! [A_89] :
      ( k5_relat_1(A_89,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_835])).

tff(c_853,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_841])).

tff(c_861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_853])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:03:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.37  
% 2.73/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.37  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.73/1.37  
% 2.73/1.37  %Foreground sorts:
% 2.73/1.37  
% 2.73/1.37  
% 2.73/1.37  %Background operators:
% 2.73/1.37  
% 2.73/1.37  
% 2.73/1.37  %Foreground operators:
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.73/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.37  
% 2.73/1.38  tff(f_92, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.73/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.73/1.38  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.73/1.38  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.73/1.38  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.73/1.38  tff(f_85, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.73/1.38  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.73/1.38  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.73/1.38  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.73/1.38  tff(f_42, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.73/1.38  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.73/1.38  tff(f_64, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.73/1.38  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.38  tff(c_32, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.73/1.38  tff(c_57, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.73/1.38  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.73/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.73/1.38  tff(c_52, plain, (![A_21]: (v1_relat_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.73/1.38  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_52])).
% 2.73/1.38  tff(c_18, plain, (![A_8, B_9]: (v1_relat_1(k5_relat_1(A_8, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.38  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.38  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.73/1.38  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.73/1.38  tff(c_211, plain, (![A_44, B_45]: (k1_relat_1(k5_relat_1(A_44, B_45))=k1_relat_1(A_44) | ~r1_tarski(k2_relat_1(A_44), k1_relat_1(B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.73/1.38  tff(c_220, plain, (![B_45]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_45))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_211])).
% 2.73/1.38  tff(c_324, plain, (![B_49]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_49))=k1_xboole_0 | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12, c_30, c_220])).
% 2.73/1.38  tff(c_20, plain, (![A_10]: (~v1_xboole_0(k1_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.73/1.38  tff(c_339, plain, (![B_49]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_49)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_49)) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_324, c_20])).
% 2.73/1.38  tff(c_390, plain, (![B_52]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_52)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_52)) | ~v1_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_339])).
% 2.73/1.38  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.73/1.38  tff(c_407, plain, (![B_53]: (k5_relat_1(k1_xboole_0, B_53)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_53)) | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_390, c_4])).
% 2.73/1.38  tff(c_414, plain, (![B_9]: (k5_relat_1(k1_xboole_0, B_9)=k1_xboole_0 | ~v1_relat_1(B_9) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_407])).
% 2.73/1.38  tff(c_431, plain, (![B_55]: (k5_relat_1(k1_xboole_0, B_55)=k1_xboole_0 | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_414])).
% 2.73/1.38  tff(c_443, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_431])).
% 2.73/1.38  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_443])).
% 2.73/1.38  tff(c_452, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.73/1.38  tff(c_458, plain, (![A_56, B_57]: (v1_xboole_0(k2_zfmisc_1(A_56, B_57)) | ~v1_xboole_0(B_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.73/1.38  tff(c_468, plain, (![A_60, B_61]: (k2_zfmisc_1(A_60, B_61)=k1_xboole_0 | ~v1_xboole_0(B_61))), inference(resolution, [status(thm)], [c_458, c_4])).
% 2.73/1.38  tff(c_474, plain, (![A_60]: (k2_zfmisc_1(A_60, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_468])).
% 2.73/1.38  tff(c_674, plain, (![B_79, A_80]: (k2_relat_1(k5_relat_1(B_79, A_80))=k2_relat_1(A_80) | ~r1_tarski(k1_relat_1(A_80), k2_relat_1(B_79)) | ~v1_relat_1(B_79) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.73/1.38  tff(c_680, plain, (![B_79]: (k2_relat_1(k5_relat_1(B_79, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_79)) | ~v1_relat_1(B_79) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_674])).
% 2.73/1.38  tff(c_690, plain, (![B_81]: (k2_relat_1(k5_relat_1(B_81, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_81))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12, c_28, c_680])).
% 2.73/1.38  tff(c_22, plain, (![A_11]: (r1_tarski(A_11, k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.38  tff(c_702, plain, (![B_81]: (r1_tarski(k5_relat_1(B_81, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_81, k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k5_relat_1(B_81, k1_xboole_0)) | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_690, c_22])).
% 2.73/1.38  tff(c_813, plain, (![B_87]: (r1_tarski(k5_relat_1(B_87, k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_87, k1_xboole_0)) | ~v1_relat_1(B_87))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_702])).
% 2.73/1.38  tff(c_504, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.73/1.38  tff(c_513, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_504])).
% 2.73/1.38  tff(c_828, plain, (![B_88]: (k5_relat_1(B_88, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_88, k1_xboole_0)) | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_813, c_513])).
% 2.73/1.38  tff(c_835, plain, (![A_8]: (k5_relat_1(A_8, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_18, c_828])).
% 2.73/1.38  tff(c_841, plain, (![A_89]: (k5_relat_1(A_89, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_835])).
% 2.73/1.38  tff(c_853, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_841])).
% 2.73/1.38  tff(c_861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_452, c_853])).
% 2.73/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  Inference rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Ref     : 0
% 2.73/1.38  #Sup     : 179
% 2.73/1.38  #Fact    : 0
% 2.73/1.38  #Define  : 0
% 2.73/1.38  #Split   : 1
% 2.73/1.38  #Chain   : 0
% 2.73/1.38  #Close   : 0
% 2.73/1.38  
% 2.73/1.38  Ordering : KBO
% 2.73/1.38  
% 2.73/1.38  Simplification rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Subsume      : 5
% 2.73/1.38  #Demod        : 197
% 2.73/1.38  #Tautology    : 117
% 2.73/1.38  #SimpNegUnit  : 2
% 2.73/1.38  #BackRed      : 0
% 2.73/1.38  
% 2.73/1.38  #Partial instantiations: 0
% 2.73/1.38  #Strategies tried      : 1
% 2.73/1.38  
% 2.73/1.38  Timing (in seconds)
% 2.73/1.38  ----------------------
% 2.73/1.39  Preprocessing        : 0.29
% 2.73/1.39  Parsing              : 0.16
% 2.73/1.39  CNF conversion       : 0.02
% 2.73/1.39  Main loop            : 0.33
% 2.73/1.39  Inferencing          : 0.13
% 2.73/1.39  Reduction            : 0.09
% 2.73/1.39  Demodulation         : 0.07
% 2.73/1.39  BG Simplification    : 0.02
% 2.73/1.39  Subsumption          : 0.07
% 2.73/1.39  Abstraction          : 0.02
% 2.73/1.39  MUC search           : 0.00
% 2.73/1.39  Cooper               : 0.00
% 2.73/1.39  Total                : 0.65
% 2.73/1.39  Index Insertion      : 0.00
% 2.73/1.39  Index Deletion       : 0.00
% 2.73/1.39  Index Matching       : 0.00
% 2.73/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
