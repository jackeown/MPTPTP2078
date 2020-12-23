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
% DateTime   : Thu Dec  3 10:00:51 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   65 (  85 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 121 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_80,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k7_relat_1(A_24,B_25))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_511,plain,(
    ! [B_91,A_92] :
      ( r1_xboole_0(k1_relat_1(B_91),A_92)
      | k7_relat_1(B_91,A_92) != k1_xboole_0
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_91,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_128,plain,(
    k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_42])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_240,plain,(
    ! [B_62,A_63] :
      ( k7_relat_1(B_62,A_63) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_62),A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_246,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_240])).

tff(c_257,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_246])).

tff(c_28,plain,(
    ! [B_27,A_26] :
      ( k2_relat_1(k7_relat_1(B_27,A_26)) = k9_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_262,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_28])).

tff(c_269,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_262])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_269])).

tff(c_273,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_520,plain,
    ( k7_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_511,c_273])).

tff(c_528,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_520])).

tff(c_10,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_323,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,k3_xboole_0(A_70,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_329,plain,(
    ! [A_73,B_74] :
      ( ~ r1_xboole_0(A_73,B_74)
      | k3_xboole_0(A_73,B_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_323])).

tff(c_333,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_329])).

tff(c_20,plain,(
    ! [A_20] : k2_zfmisc_1(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_272,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_483,plain,(
    ! [A_90] :
      ( k3_xboole_0(A_90,k2_zfmisc_1(k1_relat_1(A_90),k2_relat_1(A_90))) = A_90
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1028,plain,(
    ! [B_125,A_126] :
      ( k3_xboole_0(k7_relat_1(B_125,A_126),k2_zfmisc_1(k1_relat_1(k7_relat_1(B_125,A_126)),k9_relat_1(B_125,A_126))) = k7_relat_1(B_125,A_126)
      | ~ v1_relat_1(k7_relat_1(B_125,A_126))
      | ~ v1_relat_1(B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_483])).

tff(c_1076,plain,
    ( k3_xboole_0(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),k1_xboole_0)) = k7_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_1028])).

tff(c_1095,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_333,c_20,c_1076])).

tff(c_1096,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_528,c_1095])).

tff(c_1099,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1096])).

tff(c_1103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1099])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:00:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.56  
% 3.17/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.56  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.17/1.56  
% 3.17/1.56  %Foreground sorts:
% 3.17/1.56  
% 3.17/1.56  
% 3.17/1.56  %Background operators:
% 3.17/1.56  
% 3.17/1.56  
% 3.17/1.56  %Foreground operators:
% 3.17/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.17/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.17/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.17/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.17/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.17/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.17/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.17/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.17/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.17/1.56  
% 3.17/1.58  tff(f_93, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 3.17/1.58  tff(f_69, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.17/1.58  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.17/1.58  tff(f_80, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.17/1.58  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.17/1.58  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.17/1.58  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.17/1.58  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.17/1.58  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.17/1.58  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.17/1.58  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.17/1.58  tff(c_26, plain, (![A_24, B_25]: (v1_relat_1(k7_relat_1(A_24, B_25)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.17/1.58  tff(c_511, plain, (![B_91, A_92]: (r1_xboole_0(k1_relat_1(B_91), A_92) | k7_relat_1(B_91, A_92)!=k1_xboole_0 | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.58  tff(c_48, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.17/1.58  tff(c_91, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 3.17/1.58  tff(c_42, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.17/1.58  tff(c_128, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_91, c_42])).
% 3.17/1.58  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.17/1.58  tff(c_240, plain, (![B_62, A_63]: (k7_relat_1(B_62, A_63)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_62), A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.17/1.58  tff(c_246, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_91, c_240])).
% 3.17/1.58  tff(c_257, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_246])).
% 3.17/1.58  tff(c_28, plain, (![B_27, A_26]: (k2_relat_1(k7_relat_1(B_27, A_26))=k9_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.17/1.58  tff(c_262, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_257, c_28])).
% 3.17/1.58  tff(c_269, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_262])).
% 3.17/1.58  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_269])).
% 3.17/1.58  tff(c_273, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 3.17/1.58  tff(c_520, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_511, c_273])).
% 3.17/1.58  tff(c_528, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_520])).
% 3.17/1.58  tff(c_10, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.17/1.58  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.58  tff(c_323, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, k3_xboole_0(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.58  tff(c_329, plain, (![A_73, B_74]: (~r1_xboole_0(A_73, B_74) | k3_xboole_0(A_73, B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_323])).
% 3.17/1.58  tff(c_333, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_329])).
% 3.17/1.58  tff(c_20, plain, (![A_20]: (k2_zfmisc_1(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.17/1.58  tff(c_272, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 3.17/1.58  tff(c_483, plain, (![A_90]: (k3_xboole_0(A_90, k2_zfmisc_1(k1_relat_1(A_90), k2_relat_1(A_90)))=A_90 | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.17/1.58  tff(c_1028, plain, (![B_125, A_126]: (k3_xboole_0(k7_relat_1(B_125, A_126), k2_zfmisc_1(k1_relat_1(k7_relat_1(B_125, A_126)), k9_relat_1(B_125, A_126)))=k7_relat_1(B_125, A_126) | ~v1_relat_1(k7_relat_1(B_125, A_126)) | ~v1_relat_1(B_125))), inference(superposition, [status(thm), theory('equality')], [c_28, c_483])).
% 3.17/1.58  tff(c_1076, plain, (k3_xboole_0(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), k1_xboole_0))=k7_relat_1('#skF_4', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_272, c_1028])).
% 3.17/1.58  tff(c_1095, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_333, c_20, c_1076])).
% 3.17/1.58  tff(c_1096, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_528, c_1095])).
% 3.17/1.58  tff(c_1099, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1096])).
% 3.17/1.58  tff(c_1103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1099])).
% 3.17/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.58  
% 3.17/1.58  Inference rules
% 3.17/1.58  ----------------------
% 3.17/1.58  #Ref     : 0
% 3.17/1.58  #Sup     : 251
% 3.17/1.58  #Fact    : 0
% 3.17/1.58  #Define  : 0
% 3.17/1.58  #Split   : 4
% 3.17/1.58  #Chain   : 0
% 3.17/1.58  #Close   : 0
% 3.17/1.58  
% 3.17/1.58  Ordering : KBO
% 3.17/1.58  
% 3.17/1.58  Simplification rules
% 3.17/1.58  ----------------------
% 3.17/1.58  #Subsume      : 21
% 3.17/1.58  #Demod        : 203
% 3.17/1.58  #Tautology    : 138
% 3.17/1.58  #SimpNegUnit  : 8
% 3.17/1.58  #BackRed      : 0
% 3.17/1.58  
% 3.17/1.58  #Partial instantiations: 0
% 3.17/1.58  #Strategies tried      : 1
% 3.17/1.58  
% 3.17/1.58  Timing (in seconds)
% 3.17/1.58  ----------------------
% 3.17/1.58  Preprocessing        : 0.35
% 3.17/1.58  Parsing              : 0.18
% 3.17/1.58  CNF conversion       : 0.03
% 3.17/1.58  Main loop            : 0.43
% 3.17/1.58  Inferencing          : 0.16
% 3.17/1.58  Reduction            : 0.14
% 3.17/1.58  Demodulation         : 0.10
% 3.17/1.58  BG Simplification    : 0.03
% 3.17/1.58  Subsumption          : 0.07
% 3.17/1.58  Abstraction          : 0.03
% 3.17/1.58  MUC search           : 0.00
% 3.17/1.58  Cooper               : 0.00
% 3.17/1.58  Total                : 0.81
% 3.17/1.58  Index Insertion      : 0.00
% 3.17/1.58  Index Deletion       : 0.00
% 3.17/1.58  Index Matching       : 0.00
% 3.17/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
