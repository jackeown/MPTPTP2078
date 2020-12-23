%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:41 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   60 (  80 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 ( 101 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    ! [A_39,B_40] :
      ( v1_relat_1(k7_relat_1(A_39,B_40))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,
    ( k7_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_96,plain,(
    r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6')
    | k7_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_142,plain,(
    k7_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_50])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_xboole_0(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_20,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_190,plain,(
    ! [B_74,A_75] :
      ( k3_xboole_0(k1_relat_1(B_74),A_75) = k1_relat_1(k7_relat_1(B_74,A_75))
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_128,plain,(
    k3_xboole_0(k1_relat_1('#skF_7'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_117])).

tff(c_202,plain,
    ( k1_relat_1(k7_relat_1('#skF_7','#skF_6')) = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_128])).

tff(c_222,plain,(
    k1_relat_1(k7_relat_1('#skF_7','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_202])).

tff(c_40,plain,(
    ! [A_41] :
      ( k3_xboole_0(A_41,k2_zfmisc_1(k1_relat_1(A_41),k2_relat_1(A_41))) = A_41
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_260,plain,
    ( k3_xboole_0(k7_relat_1('#skF_7','#skF_6'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1('#skF_7','#skF_6')))) = k7_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_40])).

tff(c_266,plain,
    ( k7_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_20,c_260])).

tff(c_267,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_266])).

tff(c_271,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_267])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_271])).

tff(c_276,plain,(
    k7_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_391,plain,(
    ! [B_102,A_103] :
      ( k3_xboole_0(k1_relat_1(B_102),A_103) = k1_relat_1(k7_relat_1(B_102,A_103))
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_299,plain,(
    ! [A_81,B_82] :
      ( r1_xboole_0(A_81,B_82)
      | k3_xboole_0(A_81,B_82) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_283,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_50])).

tff(c_303,plain,(
    k3_xboole_0(k1_relat_1('#skF_7'),'#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_299,c_283])).

tff(c_407,plain,
    ( k1_relat_1(k7_relat_1('#skF_7','#skF_6')) != k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_303])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_276,c_407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 13:30:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.28  
% 2.34/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.28  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.34/1.28  
% 2.34/1.28  %Foreground sorts:
% 2.34/1.28  
% 2.34/1.28  
% 2.34/1.28  %Background operators:
% 2.34/1.28  
% 2.34/1.28  
% 2.34/1.28  %Foreground operators:
% 2.34/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.34/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.34/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.34/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.34/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.34/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.34/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.34/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.34/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.34/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.34/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.34/1.28  
% 2.34/1.29  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.34/1.29  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.34/1.29  tff(f_72, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.34/1.29  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.34/1.29  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.34/1.29  tff(f_55, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.34/1.29  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.34/1.29  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 2.34/1.29  tff(c_48, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.34/1.29  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.29  tff(c_38, plain, (![A_39, B_40]: (v1_relat_1(k7_relat_1(A_39, B_40)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.34/1.29  tff(c_56, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.34/1.29  tff(c_96, plain, (r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_56])).
% 2.34/1.29  tff(c_50, plain, (~r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6') | k7_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.34/1.29  tff(c_142, plain, (k7_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_96, c_50])).
% 2.34/1.29  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.34/1.29  tff(c_117, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.29  tff(c_129, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_117])).
% 2.34/1.29  tff(c_20, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.34/1.29  tff(c_190, plain, (![B_74, A_75]: (k3_xboole_0(k1_relat_1(B_74), A_75)=k1_relat_1(k7_relat_1(B_74, A_75)) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.34/1.29  tff(c_128, plain, (k3_xboole_0(k1_relat_1('#skF_7'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_96, c_117])).
% 2.34/1.29  tff(c_202, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_190, c_128])).
% 2.34/1.29  tff(c_222, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_202])).
% 2.34/1.29  tff(c_40, plain, (![A_41]: (k3_xboole_0(A_41, k2_zfmisc_1(k1_relat_1(A_41), k2_relat_1(A_41)))=A_41 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.34/1.29  tff(c_260, plain, (k3_xboole_0(k7_relat_1('#skF_7', '#skF_6'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k7_relat_1('#skF_7', '#skF_6'))))=k7_relat_1('#skF_7', '#skF_6') | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_40])).
% 2.34/1.29  tff(c_266, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_20, c_260])).
% 2.34/1.29  tff(c_267, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_142, c_266])).
% 2.34/1.29  tff(c_271, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_38, c_267])).
% 2.34/1.29  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_271])).
% 2.34/1.29  tff(c_276, plain, (k7_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.34/1.29  tff(c_391, plain, (![B_102, A_103]: (k3_xboole_0(k1_relat_1(B_102), A_103)=k1_relat_1(k7_relat_1(B_102, A_103)) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.34/1.29  tff(c_299, plain, (![A_81, B_82]: (r1_xboole_0(A_81, B_82) | k3_xboole_0(A_81, B_82)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.29  tff(c_283, plain, (~r1_xboole_0(k1_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_50])).
% 2.34/1.29  tff(c_303, plain, (k3_xboole_0(k1_relat_1('#skF_7'), '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_299, c_283])).
% 2.34/1.29  tff(c_407, plain, (k1_relat_1(k7_relat_1('#skF_7', '#skF_6'))!=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_391, c_303])).
% 2.34/1.29  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_276, c_407])).
% 2.34/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.29  
% 2.34/1.29  Inference rules
% 2.34/1.29  ----------------------
% 2.34/1.29  #Ref     : 0
% 2.34/1.29  #Sup     : 89
% 2.34/1.29  #Fact    : 0
% 2.34/1.29  #Define  : 0
% 2.34/1.29  #Split   : 1
% 2.34/1.29  #Chain   : 0
% 2.34/1.29  #Close   : 0
% 2.34/1.29  
% 2.34/1.29  Ordering : KBO
% 2.34/1.29  
% 2.34/1.29  Simplification rules
% 2.34/1.29  ----------------------
% 2.34/1.29  #Subsume      : 5
% 2.34/1.29  #Demod        : 29
% 2.34/1.29  #Tautology    : 56
% 2.34/1.29  #SimpNegUnit  : 4
% 2.34/1.29  #BackRed      : 0
% 2.34/1.29  
% 2.34/1.29  #Partial instantiations: 0
% 2.34/1.29  #Strategies tried      : 1
% 2.34/1.29  
% 2.34/1.29  Timing (in seconds)
% 2.34/1.29  ----------------------
% 2.34/1.30  Preprocessing        : 0.31
% 2.34/1.30  Parsing              : 0.16
% 2.34/1.30  CNF conversion       : 0.02
% 2.34/1.30  Main loop            : 0.21
% 2.34/1.30  Inferencing          : 0.08
% 2.34/1.30  Reduction            : 0.06
% 2.34/1.30  Demodulation         : 0.04
% 2.34/1.30  BG Simplification    : 0.01
% 2.34/1.30  Subsumption          : 0.04
% 2.34/1.30  Abstraction          : 0.01
% 2.34/1.30  MUC search           : 0.00
% 2.34/1.30  Cooper               : 0.00
% 2.34/1.30  Total                : 0.55
% 2.34/1.30  Index Insertion      : 0.00
% 2.34/1.30  Index Deletion       : 0.00
% 2.34/1.30  Index Matching       : 0.00
% 2.34/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
