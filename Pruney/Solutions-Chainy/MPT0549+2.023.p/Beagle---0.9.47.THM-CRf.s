%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:51 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   63 (  83 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 121 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k7_relat_1(A_18,B_19))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_556,plain,(
    ! [B_85,A_86] :
      ( r1_xboole_0(k1_relat_1(B_85),A_86)
      | k7_relat_1(B_85,A_86) != k1_xboole_0
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_89,plain,(
    k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_119,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_46])).

tff(c_294,plain,(
    ! [B_55,A_56] :
      ( k7_relat_1(B_55,A_56) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_55),A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_297,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_119,c_294])).

tff(c_307,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_297])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k9_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_312,plain,
    ( k9_relat_1('#skF_4','#skF_3') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_26])).

tff(c_319,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_312])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_319])).

tff(c_322,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_568,plain,
    ( k7_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_556,c_322])).

tff(c_577,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_568])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_346,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_352,plain,(
    ! [A_64,B_65] :
      ( ~ r1_xboole_0(A_64,B_65)
      | k3_xboole_0(A_64,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_346])).

tff(c_356,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_352])).

tff(c_18,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_323,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_490,plain,(
    ! [A_81] :
      ( k3_xboole_0(A_81,k2_zfmisc_1(k1_relat_1(A_81),k2_relat_1(A_81))) = A_81
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1315,plain,(
    ! [B_118,A_119] :
      ( k3_xboole_0(k7_relat_1(B_118,A_119),k2_zfmisc_1(k1_relat_1(k7_relat_1(B_118,A_119)),k9_relat_1(B_118,A_119))) = k7_relat_1(B_118,A_119)
      | ~ v1_relat_1(k7_relat_1(B_118,A_119))
      | ~ v1_relat_1(B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_490])).

tff(c_1369,plain,
    ( k3_xboole_0(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),k1_xboole_0)) = k7_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_1315])).

tff(c_1389,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_356,c_18,c_1369])).

tff(c_1390,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_577,c_1389])).

tff(c_1393,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1390])).

tff(c_1397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.55  
% 3.09/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.55  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.09/1.55  
% 3.09/1.55  %Foreground sorts:
% 3.09/1.55  
% 3.09/1.55  
% 3.09/1.55  %Background operators:
% 3.09/1.55  
% 3.09/1.55  
% 3.09/1.55  %Foreground operators:
% 3.09/1.55  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.09/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.09/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.09/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.09/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.09/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.09/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.09/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.09/1.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.09/1.55  
% 3.09/1.56  tff(f_91, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 3.09/1.56  tff(f_67, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.09/1.56  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.09/1.56  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.09/1.56  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.09/1.56  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.09/1.56  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.09/1.56  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.09/1.56  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.09/1.56  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.09/1.56  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.09/1.56  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k7_relat_1(A_18, B_19)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.09/1.56  tff(c_556, plain, (![B_85, A_86]: (r1_xboole_0(k1_relat_1(B_85), A_86) | k7_relat_1(B_85, A_86)!=k1_xboole_0 | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.56  tff(c_40, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.09/1.56  tff(c_89, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.09/1.56  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.56  tff(c_46, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.09/1.56  tff(c_119, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_89, c_46])).
% 3.09/1.56  tff(c_294, plain, (![B_55, A_56]: (k7_relat_1(B_55, A_56)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_55), A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.09/1.56  tff(c_297, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_119, c_294])).
% 3.09/1.56  tff(c_307, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_297])).
% 3.09/1.56  tff(c_26, plain, (![B_21, A_20]: (k2_relat_1(k7_relat_1(B_21, A_20))=k9_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.09/1.56  tff(c_312, plain, (k9_relat_1('#skF_4', '#skF_3')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_307, c_26])).
% 3.09/1.56  tff(c_319, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_312])).
% 3.09/1.56  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_319])).
% 3.09/1.56  tff(c_322, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.09/1.56  tff(c_568, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_556, c_322])).
% 3.09/1.56  tff(c_577, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_568])).
% 3.09/1.56  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.09/1.56  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.56  tff(c_346, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.09/1.56  tff(c_352, plain, (![A_64, B_65]: (~r1_xboole_0(A_64, B_65) | k3_xboole_0(A_64, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_346])).
% 3.09/1.56  tff(c_356, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_352])).
% 3.09/1.56  tff(c_18, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.09/1.56  tff(c_323, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.09/1.56  tff(c_490, plain, (![A_81]: (k3_xboole_0(A_81, k2_zfmisc_1(k1_relat_1(A_81), k2_relat_1(A_81)))=A_81 | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.09/1.56  tff(c_1315, plain, (![B_118, A_119]: (k3_xboole_0(k7_relat_1(B_118, A_119), k2_zfmisc_1(k1_relat_1(k7_relat_1(B_118, A_119)), k9_relat_1(B_118, A_119)))=k7_relat_1(B_118, A_119) | ~v1_relat_1(k7_relat_1(B_118, A_119)) | ~v1_relat_1(B_118))), inference(superposition, [status(thm), theory('equality')], [c_26, c_490])).
% 3.09/1.56  tff(c_1369, plain, (k3_xboole_0(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), k1_xboole_0))=k7_relat_1('#skF_4', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_323, c_1315])).
% 3.09/1.56  tff(c_1389, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_356, c_18, c_1369])).
% 3.09/1.56  tff(c_1390, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_577, c_1389])).
% 3.09/1.56  tff(c_1393, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1390])).
% 3.09/1.56  tff(c_1397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1393])).
% 3.09/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.56  
% 3.09/1.56  Inference rules
% 3.09/1.56  ----------------------
% 3.09/1.56  #Ref     : 0
% 3.09/1.56  #Sup     : 318
% 3.09/1.56  #Fact    : 0
% 3.09/1.56  #Define  : 0
% 3.09/1.56  #Split   : 1
% 3.09/1.56  #Chain   : 0
% 3.09/1.56  #Close   : 0
% 3.09/1.56  
% 3.09/1.56  Ordering : KBO
% 3.09/1.56  
% 3.09/1.56  Simplification rules
% 3.09/1.56  ----------------------
% 3.09/1.56  #Subsume      : 26
% 3.09/1.56  #Demod        : 305
% 3.09/1.56  #Tautology    : 181
% 3.09/1.56  #SimpNegUnit  : 10
% 3.09/1.56  #BackRed      : 1
% 3.09/1.56  
% 3.09/1.56  #Partial instantiations: 0
% 3.09/1.56  #Strategies tried      : 1
% 3.09/1.56  
% 3.09/1.56  Timing (in seconds)
% 3.09/1.56  ----------------------
% 3.09/1.56  Preprocessing        : 0.34
% 3.09/1.56  Parsing              : 0.18
% 3.09/1.56  CNF conversion       : 0.02
% 3.09/1.57  Main loop            : 0.42
% 3.09/1.57  Inferencing          : 0.16
% 3.09/1.57  Reduction            : 0.15
% 3.09/1.57  Demodulation         : 0.10
% 3.09/1.57  BG Simplification    : 0.02
% 3.09/1.57  Subsumption          : 0.07
% 3.09/1.57  Abstraction          : 0.02
% 3.09/1.57  MUC search           : 0.00
% 3.09/1.57  Cooper               : 0.00
% 3.09/1.57  Total                : 0.79
% 3.09/1.57  Index Insertion      : 0.00
% 3.09/1.57  Index Deletion       : 0.00
% 3.09/1.57  Index Matching       : 0.00
% 3.09/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
