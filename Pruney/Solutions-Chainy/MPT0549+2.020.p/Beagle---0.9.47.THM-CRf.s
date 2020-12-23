%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:50 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   58 (  86 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 142 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_439,plain,(
    ! [B_54,A_55] :
      ( r1_xboole_0(k1_relat_1(B_54),A_55)
      | k7_relat_1(B_54,A_55) != k1_xboole_0
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_69,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_130,plain,(
    ! [B_34,A_35] :
      ( k7_relat_1(B_34,A_35) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_140,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_130])).

tff(c_149,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_140])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_154,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_10])).

tff(c_164,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_154])).

tff(c_24,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_107,plain,(
    k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_24])).

tff(c_198,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_107])).

tff(c_43,plain,(
    ! [A_18] :
      ( k9_relat_1(A_18,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,(
    k9_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_43])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_38])).

tff(c_57,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_41,c_57])).

tff(c_203,plain,(
    ! [B_38] :
      ( k7_relat_1(B_38,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_62,c_130])).

tff(c_215,plain,(
    k7_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_203])).

tff(c_219,plain,
    ( k9_relat_1('#skF_2',k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_10])).

tff(c_229,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_47,c_219])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_229])).

tff(c_233,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_445,plain,
    ( k7_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_439,c_233])).

tff(c_451,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_445])).

tff(c_232,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_238,plain,(
    ! [A_39] :
      ( k2_relat_1(A_39) != k1_xboole_0
      | k1_xboole_0 = A_39
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_462,plain,(
    ! [A_58,B_59] :
      ( k2_relat_1(k7_relat_1(A_58,B_59)) != k1_xboole_0
      | k7_relat_1(A_58,B_59) = k1_xboole_0
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_8,c_238])).

tff(c_515,plain,(
    ! [B_64,A_65] :
      ( k9_relat_1(B_64,A_65) != k1_xboole_0
      | k7_relat_1(B_64,A_65) = k1_xboole_0
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_462])).

tff(c_523,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_515])).

tff(c_533,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_523])).

tff(c_535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_533])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.27  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.11/1.27  
% 2.11/1.27  %Foreground sorts:
% 2.11/1.27  
% 2.11/1.27  
% 2.11/1.27  %Background operators:
% 2.11/1.27  
% 2.11/1.27  
% 2.11/1.27  %Foreground operators:
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.11/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.11/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.27  
% 2.33/1.29  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.33/1.29  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.33/1.29  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.33/1.29  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 2.33/1.29  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.33/1.29  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.33/1.29  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.33/1.29  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.33/1.29  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.33/1.29  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.33/1.29  tff(c_439, plain, (![B_54, A_55]: (r1_xboole_0(k1_relat_1(B_54), A_55) | k7_relat_1(B_54, A_55)!=k1_xboole_0 | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.29  tff(c_30, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.33/1.29  tff(c_69, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 2.33/1.29  tff(c_130, plain, (![B_34, A_35]: (k7_relat_1(B_34, A_35)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.29  tff(c_140, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_69, c_130])).
% 2.33/1.29  tff(c_149, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_140])).
% 2.33/1.29  tff(c_10, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.29  tff(c_154, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_149, c_10])).
% 2.33/1.29  tff(c_164, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_154])).
% 2.33/1.29  tff(c_24, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.33/1.29  tff(c_107, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69, c_24])).
% 2.33/1.29  tff(c_198, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_164, c_107])).
% 2.33/1.29  tff(c_43, plain, (![A_18]: (k9_relat_1(A_18, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.33/1.29  tff(c_47, plain, (k9_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_43])).
% 2.33/1.29  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.29  tff(c_38, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.33/1.29  tff(c_41, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_38])).
% 2.33/1.29  tff(c_57, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.29  tff(c_62, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_41, c_57])).
% 2.33/1.29  tff(c_203, plain, (![B_38]: (k7_relat_1(B_38, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_62, c_130])).
% 2.33/1.29  tff(c_215, plain, (k7_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_203])).
% 2.33/1.29  tff(c_219, plain, (k9_relat_1('#skF_2', k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_215, c_10])).
% 2.33/1.29  tff(c_229, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_47, c_219])).
% 2.33/1.29  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_229])).
% 2.33/1.29  tff(c_233, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 2.33/1.29  tff(c_445, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_439, c_233])).
% 2.33/1.29  tff(c_451, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_445])).
% 2.33/1.29  tff(c_232, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.33/1.29  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.29  tff(c_238, plain, (![A_39]: (k2_relat_1(A_39)!=k1_xboole_0 | k1_xboole_0=A_39 | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.33/1.29  tff(c_462, plain, (![A_58, B_59]: (k2_relat_1(k7_relat_1(A_58, B_59))!=k1_xboole_0 | k7_relat_1(A_58, B_59)=k1_xboole_0 | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_8, c_238])).
% 2.33/1.29  tff(c_515, plain, (![B_64, A_65]: (k9_relat_1(B_64, A_65)!=k1_xboole_0 | k7_relat_1(B_64, A_65)=k1_xboole_0 | ~v1_relat_1(B_64) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_10, c_462])).
% 2.33/1.29  tff(c_523, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_232, c_515])).
% 2.33/1.29  tff(c_533, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_523])).
% 2.33/1.29  tff(c_535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_451, c_533])).
% 2.33/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.29  
% 2.33/1.29  Inference rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Ref     : 0
% 2.33/1.29  #Sup     : 121
% 2.33/1.29  #Fact    : 0
% 2.33/1.29  #Define  : 0
% 2.33/1.29  #Split   : 5
% 2.33/1.29  #Chain   : 0
% 2.33/1.29  #Close   : 0
% 2.33/1.29  
% 2.33/1.29  Ordering : KBO
% 2.33/1.29  
% 2.33/1.29  Simplification rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Subsume      : 12
% 2.33/1.29  #Demod        : 57
% 2.33/1.29  #Tautology    : 68
% 2.33/1.29  #SimpNegUnit  : 2
% 2.33/1.29  #BackRed      : 1
% 2.33/1.29  
% 2.33/1.29  #Partial instantiations: 0
% 2.33/1.29  #Strategies tried      : 1
% 2.33/1.29  
% 2.33/1.29  Timing (in seconds)
% 2.33/1.29  ----------------------
% 2.33/1.29  Preprocessing        : 0.27
% 2.33/1.29  Parsing              : 0.15
% 2.33/1.29  CNF conversion       : 0.02
% 2.33/1.29  Main loop            : 0.26
% 2.33/1.29  Inferencing          : 0.11
% 2.33/1.29  Reduction            : 0.07
% 2.33/1.29  Demodulation         : 0.05
% 2.33/1.29  BG Simplification    : 0.01
% 2.33/1.29  Subsumption          : 0.05
% 2.33/1.29  Abstraction          : 0.01
% 2.33/1.29  MUC search           : 0.00
% 2.33/1.29  Cooper               : 0.00
% 2.33/1.29  Total                : 0.56
% 2.33/1.29  Index Insertion      : 0.00
% 2.33/1.29  Index Deletion       : 0.00
% 2.33/1.29  Index Matching       : 0.00
% 2.33/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
