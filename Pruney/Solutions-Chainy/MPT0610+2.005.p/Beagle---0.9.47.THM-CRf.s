%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:37 EST 2020

% Result     : Theorem 5.02s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :   59 (  97 expanded)
%              Number of leaves         :   36 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 ( 145 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_12 > #skF_14 > #skF_10 > #skF_13 > #skF_5 > #skF_2 > #skF_7 > #skF_3 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_173,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_159,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(c_220,plain,(
    ! [A_136,B_137] :
      ( r1_xboole_0(A_136,B_137)
      | k3_xboole_0(A_136,B_137) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    ~ r1_xboole_0('#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_228,plain,(
    k3_xboole_0('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_220,c_84])).

tff(c_90,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_56,plain,(
    ! [A_90,B_91] :
      ( v1_relat_1(k3_xboole_0(A_90,B_91))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_88,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_86,plain,(
    r1_xboole_0(k1_relat_1('#skF_13'),k1_relat_1('#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_207,plain,(
    ! [A_134,B_135] :
      ( k3_xboole_0(A_134,B_135) = k1_xboole_0
      | ~ r1_xboole_0(A_134,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_211,plain,(
    k3_xboole_0(k1_relat_1('#skF_13'),k1_relat_1('#skF_14')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_207])).

tff(c_1897,plain,(
    ! [A_208,B_209] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_208,B_209)),k3_xboole_0(k1_relat_1(A_208),k1_relat_1(B_209)))
      | ~ v1_relat_1(B_209)
      | ~ v1_relat_1(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1928,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_13','#skF_14')),k1_xboole_0)
    | ~ v1_relat_1('#skF_14')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_1897])).

tff(c_1938,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_13','#skF_14')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_1928])).

tff(c_80,plain,(
    ! [B_120,A_119] :
      ( k7_relat_1(B_120,A_119) = B_120
      | ~ r1_tarski(k1_relat_1(B_120),A_119)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1947,plain,
    ( k7_relat_1(k3_xboole_0('#skF_13','#skF_14'),k1_xboole_0) = k3_xboole_0('#skF_13','#skF_14')
    | ~ v1_relat_1(k3_xboole_0('#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_1938,c_80])).

tff(c_4957,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_13','#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_1947])).

tff(c_4963,plain,(
    ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_56,c_4957])).

tff(c_4968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_4963])).

tff(c_4970,plain,(
    v1_relat_1(k3_xboole_0('#skF_13','#skF_14')) ),
    inference(splitRight,[status(thm)],[c_1947])).

tff(c_58,plain,(
    ! [A_92] :
      ( k7_relat_1(A_92,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4981,plain,(
    k7_relat_1(k3_xboole_0('#skF_13','#skF_14'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4970,c_58])).

tff(c_4969,plain,(
    k7_relat_1(k3_xboole_0('#skF_13','#skF_14'),k1_xboole_0) = k3_xboole_0('#skF_13','#skF_14') ),
    inference(splitRight,[status(thm)],[c_1947])).

tff(c_5182,plain,(
    k3_xboole_0('#skF_13','#skF_14') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4981,c_4969])).

tff(c_5183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_5182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.02/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.92  
% 5.02/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.92  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_12 > #skF_14 > #skF_10 > #skF_13 > #skF_5 > #skF_2 > #skF_7 > #skF_3 > #skF_8 > #skF_1
% 5.02/1.92  
% 5.02/1.92  %Foreground sorts:
% 5.02/1.92  
% 5.02/1.92  
% 5.02/1.92  %Background operators:
% 5.02/1.92  
% 5.02/1.92  
% 5.02/1.92  %Foreground operators:
% 5.02/1.92  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.02/1.92  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 5.02/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.02/1.92  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.02/1.92  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.02/1.92  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.02/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.02/1.92  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 5.02/1.92  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.02/1.92  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.02/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.02/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.02/1.92  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 5.02/1.92  tff('#skF_14', type, '#skF_14': $i).
% 5.02/1.92  tff('#skF_10', type, '#skF_10': $i > $i).
% 5.02/1.92  tff('#skF_13', type, '#skF_13': $i).
% 5.02/1.92  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.02/1.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.02/1.92  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.02/1.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.02/1.92  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.02/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.02/1.92  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.02/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.02/1.92  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 5.02/1.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.02/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.02/1.92  
% 5.02/1.93  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.02/1.93  tff(f_173, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 5.02/1.93  tff(f_94, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 5.02/1.93  tff(f_120, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 5.02/1.93  tff(f_159, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 5.02/1.93  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 5.02/1.93  tff(c_220, plain, (![A_136, B_137]: (r1_xboole_0(A_136, B_137) | k3_xboole_0(A_136, B_137)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.02/1.93  tff(c_84, plain, (~r1_xboole_0('#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.02/1.93  tff(c_228, plain, (k3_xboole_0('#skF_13', '#skF_14')!=k1_xboole_0), inference(resolution, [status(thm)], [c_220, c_84])).
% 5.02/1.93  tff(c_90, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.02/1.93  tff(c_56, plain, (![A_90, B_91]: (v1_relat_1(k3_xboole_0(A_90, B_91)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.02/1.93  tff(c_88, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.02/1.93  tff(c_86, plain, (r1_xboole_0(k1_relat_1('#skF_13'), k1_relat_1('#skF_14'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.02/1.93  tff(c_207, plain, (![A_134, B_135]: (k3_xboole_0(A_134, B_135)=k1_xboole_0 | ~r1_xboole_0(A_134, B_135))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.02/1.93  tff(c_211, plain, (k3_xboole_0(k1_relat_1('#skF_13'), k1_relat_1('#skF_14'))=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_207])).
% 5.02/1.93  tff(c_1897, plain, (![A_208, B_209]: (r1_tarski(k1_relat_1(k3_xboole_0(A_208, B_209)), k3_xboole_0(k1_relat_1(A_208), k1_relat_1(B_209))) | ~v1_relat_1(B_209) | ~v1_relat_1(A_208))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.02/1.93  tff(c_1928, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_13', '#skF_14')), k1_xboole_0) | ~v1_relat_1('#skF_14') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_211, c_1897])).
% 5.02/1.93  tff(c_1938, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_13', '#skF_14')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_1928])).
% 5.02/1.93  tff(c_80, plain, (![B_120, A_119]: (k7_relat_1(B_120, A_119)=B_120 | ~r1_tarski(k1_relat_1(B_120), A_119) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.02/1.93  tff(c_1947, plain, (k7_relat_1(k3_xboole_0('#skF_13', '#skF_14'), k1_xboole_0)=k3_xboole_0('#skF_13', '#skF_14') | ~v1_relat_1(k3_xboole_0('#skF_13', '#skF_14'))), inference(resolution, [status(thm)], [c_1938, c_80])).
% 5.02/1.93  tff(c_4957, plain, (~v1_relat_1(k3_xboole_0('#skF_13', '#skF_14'))), inference(splitLeft, [status(thm)], [c_1947])).
% 5.02/1.93  tff(c_4963, plain, (~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_56, c_4957])).
% 5.02/1.93  tff(c_4968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_4963])).
% 5.02/1.93  tff(c_4970, plain, (v1_relat_1(k3_xboole_0('#skF_13', '#skF_14'))), inference(splitRight, [status(thm)], [c_1947])).
% 5.02/1.93  tff(c_58, plain, (![A_92]: (k7_relat_1(A_92, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.02/1.93  tff(c_4981, plain, (k7_relat_1(k3_xboole_0('#skF_13', '#skF_14'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4970, c_58])).
% 5.02/1.93  tff(c_4969, plain, (k7_relat_1(k3_xboole_0('#skF_13', '#skF_14'), k1_xboole_0)=k3_xboole_0('#skF_13', '#skF_14')), inference(splitRight, [status(thm)], [c_1947])).
% 5.02/1.93  tff(c_5182, plain, (k3_xboole_0('#skF_13', '#skF_14')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4981, c_4969])).
% 5.02/1.93  tff(c_5183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_228, c_5182])).
% 5.02/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.93  
% 5.02/1.93  Inference rules
% 5.02/1.93  ----------------------
% 5.02/1.93  #Ref     : 1
% 5.02/1.93  #Sup     : 1110
% 5.02/1.93  #Fact    : 0
% 5.02/1.93  #Define  : 0
% 5.02/1.93  #Split   : 5
% 5.02/1.93  #Chain   : 0
% 5.02/1.93  #Close   : 0
% 5.02/1.93  
% 5.02/1.93  Ordering : KBO
% 5.02/1.93  
% 5.02/1.93  Simplification rules
% 5.02/1.93  ----------------------
% 5.02/1.93  #Subsume      : 105
% 5.02/1.93  #Demod        : 1297
% 5.02/1.93  #Tautology    : 716
% 5.02/1.93  #SimpNegUnit  : 7
% 5.02/1.93  #BackRed      : 27
% 5.02/1.93  
% 5.02/1.93  #Partial instantiations: 0
% 5.02/1.93  #Strategies tried      : 1
% 5.02/1.93  
% 5.02/1.93  Timing (in seconds)
% 5.02/1.93  ----------------------
% 5.02/1.94  Preprocessing        : 0.36
% 5.02/1.94  Parsing              : 0.19
% 5.02/1.94  CNF conversion       : 0.03
% 5.02/1.94  Main loop            : 0.81
% 5.02/1.94  Inferencing          : 0.29
% 5.02/1.94  Reduction            : 0.28
% 5.02/1.94  Demodulation         : 0.20
% 5.02/1.94  BG Simplification    : 0.04
% 5.02/1.94  Subsumption          : 0.15
% 5.02/1.94  Abstraction          : 0.05
% 5.02/1.94  MUC search           : 0.00
% 5.02/1.94  Cooper               : 0.00
% 5.02/1.94  Total                : 1.20
% 5.02/1.94  Index Insertion      : 0.00
% 5.02/1.94  Index Deletion       : 0.00
% 5.02/1.94  Index Matching       : 0.00
% 5.02/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
