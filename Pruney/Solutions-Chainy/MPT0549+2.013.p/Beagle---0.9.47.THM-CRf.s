%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:49 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 115 expanded)
%              Number of equality atoms :   32 (  46 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_40,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_185,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(k1_relat_1(B_38),A_39)
      | k7_relat_1(B_38,A_39) != k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_24,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_64,plain,(
    k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_24])).

tff(c_8,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    ! [B_24,A_25] :
      ( k7_relat_1(B_24,A_25) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_24),A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_106])).

tff(c_115,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_109])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_6])).

tff(c_126,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8,c_119])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_126])).

tff(c_130,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_191,plain,
    ( k7_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_185,c_130])).

tff(c_198,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_191])).

tff(c_129,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,(
    ! [A_32,B_33] :
      ( k5_relat_1(k6_relat_1(A_32),B_33) = k7_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ! [B_33,A_32] :
      ( v1_relat_1(k7_relat_1(B_33,A_32))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_171,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(k7_relat_1(B_34,A_35))
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_163])).

tff(c_12,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_199,plain,(
    ! [B_40,A_41] :
      ( k2_relat_1(k7_relat_1(B_40,A_41)) != k1_xboole_0
      | k7_relat_1(B_40,A_41) = k1_xboole_0
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_171,c_12])).

tff(c_204,plain,(
    ! [B_44,A_45] :
      ( k9_relat_1(B_44,A_45) != k1_xboole_0
      | k7_relat_1(B_44,A_45) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_199])).

tff(c_206,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_204])).

tff(c_209,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_206])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.61  
% 2.26/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.61  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.26/1.61  
% 2.26/1.61  %Foreground sorts:
% 2.26/1.61  
% 2.26/1.61  
% 2.26/1.61  %Background operators:
% 2.26/1.61  
% 2.26/1.61  
% 2.26/1.61  %Foreground operators:
% 2.26/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.26/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.26/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.61  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.26/1.61  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.26/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.61  
% 2.26/1.63  tff(f_65, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.26/1.63  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.26/1.63  tff(f_40, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.26/1.63  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.26/1.63  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.26/1.63  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.26/1.63  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.26/1.63  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.26/1.63  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.63  tff(c_185, plain, (![B_38, A_39]: (r1_xboole_0(k1_relat_1(B_38), A_39) | k7_relat_1(B_38, A_39)!=k1_xboole_0 | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.26/1.63  tff(c_30, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.63  tff(c_60, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 2.26/1.63  tff(c_24, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.63  tff(c_64, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_24])).
% 2.26/1.63  tff(c_8, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.63  tff(c_106, plain, (![B_24, A_25]: (k7_relat_1(B_24, A_25)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_24), A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.26/1.63  tff(c_109, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_106])).
% 2.26/1.63  tff(c_115, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_109])).
% 2.26/1.63  tff(c_6, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.63  tff(c_119, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_115, c_6])).
% 2.26/1.63  tff(c_126, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8, c_119])).
% 2.26/1.63  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_126])).
% 2.26/1.63  tff(c_130, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 2.26/1.63  tff(c_191, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_185, c_130])).
% 2.26/1.63  tff(c_198, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_191])).
% 2.26/1.63  tff(c_129, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.26/1.63  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.63  tff(c_157, plain, (![A_32, B_33]: (k5_relat_1(k6_relat_1(A_32), B_33)=k7_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.26/1.63  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.63  tff(c_163, plain, (![B_33, A_32]: (v1_relat_1(k7_relat_1(B_33, A_32)) | ~v1_relat_1(B_33) | ~v1_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 2.26/1.63  tff(c_171, plain, (![B_34, A_35]: (v1_relat_1(k7_relat_1(B_34, A_35)) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_163])).
% 2.26/1.63  tff(c_12, plain, (![A_6]: (k2_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.63  tff(c_199, plain, (![B_40, A_41]: (k2_relat_1(k7_relat_1(B_40, A_41))!=k1_xboole_0 | k7_relat_1(B_40, A_41)=k1_xboole_0 | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_171, c_12])).
% 2.26/1.63  tff(c_204, plain, (![B_44, A_45]: (k9_relat_1(B_44, A_45)!=k1_xboole_0 | k7_relat_1(B_44, A_45)=k1_xboole_0 | ~v1_relat_1(B_44) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_6, c_199])).
% 2.26/1.63  tff(c_206, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_129, c_204])).
% 2.26/1.63  tff(c_209, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_206])).
% 2.26/1.63  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_209])).
% 2.26/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.63  
% 2.26/1.63  Inference rules
% 2.26/1.63  ----------------------
% 2.26/1.63  #Ref     : 0
% 2.26/1.63  #Sup     : 40
% 2.26/1.63  #Fact    : 0
% 2.26/1.63  #Define  : 0
% 2.26/1.63  #Split   : 4
% 2.53/1.63  #Chain   : 0
% 2.53/1.63  #Close   : 0
% 2.53/1.63  
% 2.53/1.63  Ordering : KBO
% 2.53/1.63  
% 2.53/1.63  Simplification rules
% 2.53/1.63  ----------------------
% 2.53/1.63  #Subsume      : 2
% 2.53/1.63  #Demod        : 9
% 2.53/1.63  #Tautology    : 18
% 2.53/1.63  #SimpNegUnit  : 2
% 2.53/1.63  #BackRed      : 0
% 2.53/1.63  
% 2.53/1.63  #Partial instantiations: 0
% 2.53/1.63  #Strategies tried      : 1
% 2.53/1.63  
% 2.53/1.63  Timing (in seconds)
% 2.53/1.63  ----------------------
% 2.53/1.64  Preprocessing        : 0.44
% 2.53/1.64  Parsing              : 0.24
% 2.53/1.64  CNF conversion       : 0.03
% 2.53/1.64  Main loop            : 0.29
% 2.53/1.64  Inferencing          : 0.12
% 2.53/1.64  Reduction            : 0.07
% 2.53/1.64  Demodulation         : 0.05
% 2.53/1.64  BG Simplification    : 0.02
% 2.53/1.64  Subsumption          : 0.06
% 2.53/1.64  Abstraction          : 0.01
% 2.53/1.64  MUC search           : 0.00
% 2.53/1.64  Cooper               : 0.00
% 2.53/1.64  Total                : 0.77
% 2.53/1.64  Index Insertion      : 0.00
% 2.53/1.64  Index Deletion       : 0.00
% 2.53/1.64  Index Matching       : 0.00
% 2.53/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
