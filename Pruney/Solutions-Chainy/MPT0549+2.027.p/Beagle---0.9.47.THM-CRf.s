%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:51 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 112 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 184 expanded)
%              Number of equality atoms :   48 (  87 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_419,plain,(
    ! [B_59,A_60] :
      ( r1_xboole_0(k1_relat_1(B_59),A_60)
      | k7_relat_1(B_59,A_60) != k1_xboole_0
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_77,plain,(
    k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_94,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_36])).

tff(c_195,plain,(
    ! [B_36,A_37] :
      ( k7_relat_1(B_36,A_37) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_198,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_195])).

tff(c_205,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_198])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_210,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_16])).

tff(c_220,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_210])).

tff(c_246,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_77])).

tff(c_53,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_57,plain,(
    k9_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_103])).

tff(c_124,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_121])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_8])).

tff(c_118,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_2')) = k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_103])).

tff(c_132,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_118])).

tff(c_284,plain,(
    ! [B_42,A_43] :
      ( k9_relat_1(B_42,k3_xboole_0(k1_relat_1(B_42),A_43)) = k9_relat_1(B_42,A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_293,plain,
    ( k9_relat_1('#skF_2',k1_xboole_0) = k9_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_284])).

tff(c_305,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_220,c_57,c_293])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_305])).

tff(c_308,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_428,plain,
    ( k7_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_419,c_308])).

tff(c_433,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_428])).

tff(c_309,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_314,plain,(
    ! [A_44] :
      ( k2_relat_1(A_44) != k1_xboole_0
      | k1_xboole_0 = A_44
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_474,plain,(
    ! [A_65,B_66] :
      ( k2_relat_1(k7_relat_1(A_65,B_66)) != k1_xboole_0
      | k7_relat_1(A_65,B_66) = k1_xboole_0
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_12,c_314])).

tff(c_829,plain,(
    ! [B_82,A_83] :
      ( k9_relat_1(B_82,A_83) != k1_xboole_0
      | k7_relat_1(B_82,A_83) = k1_xboole_0
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_474])).

tff(c_837,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_829])).

tff(c_846,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_837])).

tff(c_848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.52  
% 2.74/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.52  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.74/1.52  
% 2.74/1.52  %Foreground sorts:
% 2.74/1.52  
% 2.74/1.52  
% 2.74/1.52  %Background operators:
% 2.74/1.52  
% 2.74/1.52  
% 2.74/1.52  %Foreground operators:
% 2.74/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.74/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.74/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.74/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.52  
% 2.92/1.53  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.92/1.53  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.92/1.53  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.92/1.53  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 2.92/1.53  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.92/1.53  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.92/1.53  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.92/1.53  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.92/1.53  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 2.92/1.53  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.92/1.53  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.92/1.53  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.92/1.53  tff(c_419, plain, (![B_59, A_60]: (r1_xboole_0(k1_relat_1(B_59), A_60) | k7_relat_1(B_59, A_60)!=k1_xboole_0 | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.92/1.53  tff(c_30, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.92/1.53  tff(c_77, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 2.92/1.53  tff(c_36, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.92/1.53  tff(c_94, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_77, c_36])).
% 2.92/1.53  tff(c_195, plain, (![B_36, A_37]: (k7_relat_1(B_36, A_37)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.92/1.53  tff(c_198, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_94, c_195])).
% 2.92/1.53  tff(c_205, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_198])).
% 2.92/1.53  tff(c_16, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.53  tff(c_210, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_205, c_16])).
% 2.92/1.53  tff(c_220, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_210])).
% 2.92/1.53  tff(c_246, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_220, c_77])).
% 2.92/1.53  tff(c_53, plain, (![A_19]: (k9_relat_1(A_19, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.92/1.53  tff(c_57, plain, (k9_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_53])).
% 2.92/1.53  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.53  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.92/1.53  tff(c_103, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.53  tff(c_121, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_103])).
% 2.92/1.53  tff(c_124, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_121])).
% 2.92/1.53  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.53  tff(c_98, plain, (k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_94, c_8])).
% 2.92/1.53  tff(c_118, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_2'))=k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_98, c_103])).
% 2.92/1.53  tff(c_132, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_124, c_118])).
% 2.92/1.53  tff(c_284, plain, (![B_42, A_43]: (k9_relat_1(B_42, k3_xboole_0(k1_relat_1(B_42), A_43))=k9_relat_1(B_42, A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.92/1.53  tff(c_293, plain, (k9_relat_1('#skF_2', k1_xboole_0)=k9_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_132, c_284])).
% 2.92/1.53  tff(c_305, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_220, c_57, c_293])).
% 2.92/1.53  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_305])).
% 2.92/1.53  tff(c_308, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 2.92/1.53  tff(c_428, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_419, c_308])).
% 2.92/1.53  tff(c_433, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_428])).
% 2.92/1.53  tff(c_309, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.92/1.53  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.53  tff(c_314, plain, (![A_44]: (k2_relat_1(A_44)!=k1_xboole_0 | k1_xboole_0=A_44 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.92/1.53  tff(c_474, plain, (![A_65, B_66]: (k2_relat_1(k7_relat_1(A_65, B_66))!=k1_xboole_0 | k7_relat_1(A_65, B_66)=k1_xboole_0 | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_12, c_314])).
% 2.92/1.53  tff(c_829, plain, (![B_82, A_83]: (k9_relat_1(B_82, A_83)!=k1_xboole_0 | k7_relat_1(B_82, A_83)=k1_xboole_0 | ~v1_relat_1(B_82) | ~v1_relat_1(B_82))), inference(superposition, [status(thm), theory('equality')], [c_16, c_474])).
% 2.92/1.53  tff(c_837, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_309, c_829])).
% 2.92/1.53  tff(c_846, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_837])).
% 2.92/1.53  tff(c_848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_433, c_846])).
% 2.92/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.53  
% 2.92/1.53  Inference rules
% 2.92/1.53  ----------------------
% 2.92/1.53  #Ref     : 0
% 2.92/1.53  #Sup     : 195
% 2.92/1.53  #Fact    : 0
% 2.92/1.53  #Define  : 0
% 2.92/1.53  #Split   : 4
% 2.92/1.53  #Chain   : 0
% 2.92/1.53  #Close   : 0
% 2.92/1.53  
% 2.92/1.53  Ordering : KBO
% 2.92/1.53  
% 2.92/1.53  Simplification rules
% 2.92/1.53  ----------------------
% 2.92/1.53  #Subsume      : 10
% 2.92/1.53  #Demod        : 90
% 2.92/1.53  #Tautology    : 123
% 2.92/1.53  #SimpNegUnit  : 4
% 2.92/1.53  #BackRed      : 2
% 2.92/1.53  
% 2.92/1.53  #Partial instantiations: 0
% 2.92/1.53  #Strategies tried      : 1
% 2.92/1.53  
% 2.92/1.53  Timing (in seconds)
% 2.92/1.53  ----------------------
% 2.99/1.54  Preprocessing        : 0.35
% 2.99/1.54  Parsing              : 0.18
% 2.99/1.54  CNF conversion       : 0.02
% 2.99/1.54  Main loop            : 0.35
% 2.99/1.54  Inferencing          : 0.14
% 2.99/1.54  Reduction            : 0.10
% 2.99/1.54  Demodulation         : 0.07
% 2.99/1.54  BG Simplification    : 0.02
% 2.99/1.54  Subsumption          : 0.06
% 2.99/1.54  Abstraction          : 0.02
% 2.99/1.54  MUC search           : 0.00
% 2.99/1.54  Cooper               : 0.00
% 2.99/1.54  Total                : 0.73
% 2.99/1.54  Index Insertion      : 0.00
% 2.99/1.54  Index Deletion       : 0.00
% 2.99/1.54  Index Matching       : 0.00
% 2.99/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
