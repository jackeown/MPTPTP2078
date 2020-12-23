%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:07 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  98 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 172 expanded)
%              Number of equality atoms :   36 (  56 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_32,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_53,plain,(
    ! [A_19] :
      ( v1_relat_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_53])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_123,plain,(
    ! [A_29,B_30] :
      ( k1_relat_1(k5_relat_1(A_29,B_30)) = k1_relat_1(A_29)
      | ~ r1_tarski(k2_relat_1(A_29),k1_relat_1(B_30))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_129,plain,(
    ! [B_30] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_30)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_30))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_123])).

tff(c_134,plain,(
    ! [B_31] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_31)) = k1_xboole_0
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_10,c_30,c_129])).

tff(c_22,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k2_zfmisc_1(k1_relat_1(A_9),k2_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_143,plain,(
    ! [B_31] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_31),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_31))))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_22])).

tff(c_187,plain,(
    ! [B_35] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_35),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_143])).

tff(c_85,plain,(
    ! [B_23,A_24] :
      ( B_23 = A_24
      | ~ r1_tarski(B_23,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_197,plain,(
    ! [B_36] :
      ( k5_relat_1(k1_xboole_0,B_36) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_187,c_94])).

tff(c_201,plain,(
    ! [B_8] :
      ( k5_relat_1(k1_xboole_0,B_8) = k1_xboole_0
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_197])).

tff(c_205,plain,(
    ! [B_37] :
      ( k5_relat_1(k1_xboole_0,B_37) = k1_xboole_0
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_201])).

tff(c_214,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_205])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_214])).

tff(c_221,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_296,plain,(
    ! [B_47,A_48] :
      ( k2_relat_1(k5_relat_1(B_47,A_48)) = k2_relat_1(A_48)
      | ~ r1_tarski(k1_relat_1(A_48),k2_relat_1(B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_299,plain,(
    ! [B_47] :
      ( k2_relat_1(k5_relat_1(B_47,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_296])).

tff(c_307,plain,(
    ! [B_49] :
      ( k2_relat_1(k5_relat_1(B_49,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_10,c_28,c_299])).

tff(c_316,plain,(
    ! [B_49] :
      ( r1_tarski(k5_relat_1(B_49,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_49,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(B_49,k1_xboole_0))
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_22])).

tff(c_323,plain,(
    ! [B_50] :
      ( r1_tarski(k5_relat_1(B_50,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_50,k1_xboole_0))
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_316])).

tff(c_253,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_262,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_253])).

tff(c_375,plain,(
    ! [B_54] :
      ( k5_relat_1(B_54,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_54,k1_xboole_0))
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_323,c_262])).

tff(c_379,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_20,c_375])).

tff(c_383,plain,(
    ! [A_55] :
      ( k5_relat_1(A_55,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_379])).

tff(c_392,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_383])).

tff(c_398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:58:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.32  
% 2.21/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.33  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.21/1.33  
% 2.21/1.33  %Foreground sorts:
% 2.21/1.33  
% 2.21/1.33  
% 2.21/1.33  %Background operators:
% 2.21/1.33  
% 2.21/1.33  
% 2.21/1.33  %Foreground operators:
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.21/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.33  
% 2.21/1.34  tff(f_82, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.21/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.21/1.34  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.21/1.34  tff(f_50, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.21/1.34  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.21/1.34  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.21/1.34  tff(f_75, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.21/1.34  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.21/1.34  tff(f_54, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.21/1.34  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.21/1.34  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.21/1.34  tff(c_32, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.21/1.34  tff(c_58, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.21/1.34  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.21/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.21/1.34  tff(c_53, plain, (![A_19]: (v1_relat_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.34  tff(c_57, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_53])).
% 2.21/1.34  tff(c_20, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.34  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.21/1.34  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.21/1.34  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.34  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.34  tff(c_123, plain, (![A_29, B_30]: (k1_relat_1(k5_relat_1(A_29, B_30))=k1_relat_1(A_29) | ~r1_tarski(k2_relat_1(A_29), k1_relat_1(B_30)) | ~v1_relat_1(B_30) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.21/1.34  tff(c_129, plain, (![B_30]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_30))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_30)) | ~v1_relat_1(B_30) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_123])).
% 2.21/1.34  tff(c_134, plain, (![B_31]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_31))=k1_xboole_0 | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_10, c_30, c_129])).
% 2.21/1.34  tff(c_22, plain, (![A_9]: (r1_tarski(A_9, k2_zfmisc_1(k1_relat_1(A_9), k2_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.34  tff(c_143, plain, (![B_31]: (r1_tarski(k5_relat_1(k1_xboole_0, B_31), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_31)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_31)) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_134, c_22])).
% 2.21/1.34  tff(c_187, plain, (![B_35]: (r1_tarski(k5_relat_1(k1_xboole_0, B_35), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_35)) | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_143])).
% 2.21/1.34  tff(c_85, plain, (![B_23, A_24]: (B_23=A_24 | ~r1_tarski(B_23, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.34  tff(c_94, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_85])).
% 2.21/1.34  tff(c_197, plain, (![B_36]: (k5_relat_1(k1_xboole_0, B_36)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_36)) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_187, c_94])).
% 2.21/1.34  tff(c_201, plain, (![B_8]: (k5_relat_1(k1_xboole_0, B_8)=k1_xboole_0 | ~v1_relat_1(B_8) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_197])).
% 2.21/1.34  tff(c_205, plain, (![B_37]: (k5_relat_1(k1_xboole_0, B_37)=k1_xboole_0 | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_201])).
% 2.21/1.34  tff(c_214, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_205])).
% 2.21/1.34  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_214])).
% 2.21/1.34  tff(c_221, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.21/1.34  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.21/1.34  tff(c_296, plain, (![B_47, A_48]: (k2_relat_1(k5_relat_1(B_47, A_48))=k2_relat_1(A_48) | ~r1_tarski(k1_relat_1(A_48), k2_relat_1(B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.34  tff(c_299, plain, (![B_47]: (k2_relat_1(k5_relat_1(B_47, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_296])).
% 2.21/1.34  tff(c_307, plain, (![B_49]: (k2_relat_1(k5_relat_1(B_49, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_10, c_28, c_299])).
% 2.21/1.34  tff(c_316, plain, (![B_49]: (r1_tarski(k5_relat_1(B_49, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_49, k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k5_relat_1(B_49, k1_xboole_0)) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_307, c_22])).
% 2.21/1.34  tff(c_323, plain, (![B_50]: (r1_tarski(k5_relat_1(B_50, k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_50, k1_xboole_0)) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_316])).
% 2.21/1.34  tff(c_253, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.34  tff(c_262, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_253])).
% 2.21/1.34  tff(c_375, plain, (![B_54]: (k5_relat_1(B_54, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_54, k1_xboole_0)) | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_323, c_262])).
% 2.21/1.34  tff(c_379, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_20, c_375])).
% 2.21/1.34  tff(c_383, plain, (![A_55]: (k5_relat_1(A_55, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_379])).
% 2.21/1.34  tff(c_392, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_383])).
% 2.21/1.34  tff(c_398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_392])).
% 2.21/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.34  
% 2.21/1.34  Inference rules
% 2.21/1.34  ----------------------
% 2.21/1.34  #Ref     : 0
% 2.21/1.34  #Sup     : 77
% 2.21/1.34  #Fact    : 0
% 2.21/1.34  #Define  : 0
% 2.21/1.34  #Split   : 1
% 2.21/1.34  #Chain   : 0
% 2.21/1.34  #Close   : 0
% 2.21/1.34  
% 2.21/1.34  Ordering : KBO
% 2.21/1.34  
% 2.21/1.34  Simplification rules
% 2.21/1.34  ----------------------
% 2.21/1.34  #Subsume      : 2
% 2.21/1.34  #Demod        : 47
% 2.21/1.34  #Tautology    : 41
% 2.21/1.34  #SimpNegUnit  : 2
% 2.21/1.34  #BackRed      : 0
% 2.21/1.34  
% 2.21/1.34  #Partial instantiations: 0
% 2.21/1.34  #Strategies tried      : 1
% 2.21/1.34  
% 2.21/1.34  Timing (in seconds)
% 2.21/1.34  ----------------------
% 2.21/1.34  Preprocessing        : 0.30
% 2.21/1.34  Parsing              : 0.17
% 2.21/1.35  CNF conversion       : 0.02
% 2.21/1.35  Main loop            : 0.21
% 2.21/1.35  Inferencing          : 0.08
% 2.21/1.35  Reduction            : 0.06
% 2.21/1.35  Demodulation         : 0.04
% 2.21/1.35  BG Simplification    : 0.01
% 2.21/1.35  Subsumption          : 0.04
% 2.21/1.35  Abstraction          : 0.01
% 2.21/1.35  MUC search           : 0.00
% 2.21/1.35  Cooper               : 0.00
% 2.21/1.35  Total                : 0.55
% 2.21/1.35  Index Insertion      : 0.00
% 2.21/1.35  Index Deletion       : 0.00
% 2.21/1.35  Index Matching       : 0.00
% 2.21/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
