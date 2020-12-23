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
% DateTime   : Thu Dec  3 09:59:42 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 105 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 ( 143 expanded)
%              Number of equality atoms :   29 (  60 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_88,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_97,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_98,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_98])).

tff(c_36,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(k7_relat_1(A_44,B_45))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [B_41] : k2_zfmisc_1(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_206,plain,(
    ! [B_78,A_79] :
      ( k3_xboole_0(k1_relat_1(B_78),A_79) = k1_relat_1(k7_relat_1(B_78,A_79))
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_154,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_54])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_158,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_2])).

tff(c_215,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_158])).

tff(c_238,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_215])).

tff(c_38,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,k2_zfmisc_1(k1_relat_1(A_46),k2_relat_1(A_46)))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_248,plain,
    ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1('#skF_4','#skF_3'))))
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_38])).

tff(c_251,plain,
    ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_248])).

tff(c_270,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_273,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_270])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_273])).

tff(c_278,plain,(
    r1_tarski(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_291,plain,(
    k3_xboole_0(k7_relat_1('#skF_4','#skF_3'),k1_xboole_0) = k7_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_12])).

tff(c_293,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_291])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_293])).

tff(c_297,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_399,plain,(
    ! [B_104,A_105] :
      ( k3_xboole_0(k1_relat_1(B_104),A_105) = k1_relat_1(k7_relat_1(B_104,A_105))
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_330,plain,(
    ! [A_90,B_91] :
      ( r1_xboole_0(A_90,B_91)
      | k3_xboole_0(A_90,B_91) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_296,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_338,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_330,c_296])).

tff(c_408,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_338])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_297,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.16/1.30  
% 2.16/1.30  %Foreground sorts:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Background operators:
% 2.16/1.30  
% 2.16/1.30  
% 2.16/1.30  %Foreground operators:
% 2.16/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.16/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.30  
% 2.16/1.31  tff(f_99, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.16/1.31  tff(f_88, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.16/1.31  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.16/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.16/1.31  tff(f_81, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.16/1.31  tff(f_75, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.16/1.31  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.16/1.31  tff(f_85, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.16/1.31  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.16/1.31  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.16/1.31  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.16/1.31  tff(c_48, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.16/1.31  tff(c_97, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.16/1.31  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.31  tff(c_98, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.31  tff(c_102, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_98])).
% 2.16/1.31  tff(c_36, plain, (![A_44, B_45]: (v1_relat_1(k7_relat_1(A_44, B_45)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.16/1.31  tff(c_32, plain, (![B_41]: (k2_zfmisc_1(k1_xboole_0, B_41)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.16/1.31  tff(c_206, plain, (![B_78, A_79]: (k3_xboole_0(k1_relat_1(B_78), A_79)=k1_relat_1(k7_relat_1(B_78, A_79)) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.16/1.31  tff(c_54, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.16/1.31  tff(c_154, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_97, c_54])).
% 2.16/1.31  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.31  tff(c_158, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_2])).
% 2.16/1.31  tff(c_215, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_206, c_158])).
% 2.16/1.31  tff(c_238, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_215])).
% 2.16/1.31  tff(c_38, plain, (![A_46]: (r1_tarski(A_46, k2_zfmisc_1(k1_relat_1(A_46), k2_relat_1(A_46))) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.16/1.31  tff(c_248, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k7_relat_1('#skF_4', '#skF_3')))) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_38])).
% 2.16/1.31  tff(c_251, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_248])).
% 2.16/1.31  tff(c_270, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_251])).
% 2.16/1.31  tff(c_273, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_270])).
% 2.16/1.31  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_273])).
% 2.16/1.31  tff(c_278, plain, (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_251])).
% 2.16/1.31  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.31  tff(c_291, plain, (k3_xboole_0(k7_relat_1('#skF_4', '#skF_3'), k1_xboole_0)=k7_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_278, c_12])).
% 2.16/1.31  tff(c_293, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_102, c_291])).
% 2.16/1.31  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_293])).
% 2.16/1.31  tff(c_297, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.16/1.31  tff(c_399, plain, (![B_104, A_105]: (k3_xboole_0(k1_relat_1(B_104), A_105)=k1_relat_1(k7_relat_1(B_104, A_105)) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.16/1.31  tff(c_330, plain, (![A_90, B_91]: (r1_xboole_0(A_90, B_91) | k3_xboole_0(A_90, B_91)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.31  tff(c_296, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 2.16/1.31  tff(c_338, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_330, c_296])).
% 2.16/1.31  tff(c_408, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_399, c_338])).
% 2.16/1.31  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_297, c_408])).
% 2.16/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  Inference rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Ref     : 0
% 2.16/1.31  #Sup     : 84
% 2.16/1.31  #Fact    : 0
% 2.16/1.31  #Define  : 0
% 2.16/1.31  #Split   : 3
% 2.16/1.31  #Chain   : 0
% 2.16/1.31  #Close   : 0
% 2.16/1.31  
% 2.16/1.31  Ordering : KBO
% 2.16/1.31  
% 2.16/1.31  Simplification rules
% 2.16/1.31  ----------------------
% 2.16/1.31  #Subsume      : 6
% 2.16/1.31  #Demod        : 27
% 2.16/1.31  #Tautology    : 54
% 2.16/1.31  #SimpNegUnit  : 5
% 2.16/1.31  #BackRed      : 0
% 2.16/1.31  
% 2.16/1.31  #Partial instantiations: 0
% 2.16/1.31  #Strategies tried      : 1
% 2.16/1.31  
% 2.16/1.31  Timing (in seconds)
% 2.16/1.31  ----------------------
% 2.16/1.32  Preprocessing        : 0.33
% 2.16/1.32  Parsing              : 0.18
% 2.16/1.32  CNF conversion       : 0.02
% 2.16/1.32  Main loop            : 0.21
% 2.16/1.32  Inferencing          : 0.08
% 2.16/1.32  Reduction            : 0.06
% 2.16/1.32  Demodulation         : 0.05
% 2.16/1.32  BG Simplification    : 0.02
% 2.16/1.32  Subsumption          : 0.03
% 2.16/1.32  Abstraction          : 0.01
% 2.16/1.32  MUC search           : 0.00
% 2.16/1.32  Cooper               : 0.00
% 2.16/1.32  Total                : 0.57
% 2.16/1.32  Index Insertion      : 0.00
% 2.16/1.32  Index Deletion       : 0.00
% 2.16/1.32  Index Matching       : 0.00
% 2.16/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
