%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:00 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   59 (  89 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 ( 104 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_48,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_93,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_394,plain,(
    ! [A_119,B_120] :
      ( r2_hidden(k4_tarski('#skF_2'(A_119,B_120),'#skF_1'(A_119,B_120)),A_119)
      | r2_hidden('#skF_3'(A_119,B_120),B_120)
      | k2_relat_1(A_119) = B_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_94,plain,(
    ! [C_62,B_63] : ~ r2_hidden(C_62,k4_xboole_0(B_63,k1_tarski(C_62))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_94])).

tff(c_449,plain,(
    ! [B_121] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_121),B_121)
      | k2_relat_1(k1_xboole_0) = B_121 ) ),
    inference(resolution,[status(thm)],[c_394,c_97])).

tff(c_500,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_449,c_97])).

tff(c_57,plain,(
    ! [B_59] : k2_zfmisc_1(k1_xboole_0,B_59) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [A_51,B_52] : v1_relat_1(k2_zfmisc_1(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_44])).

tff(c_46,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_5'(A_53,B_54),k2_relat_1(B_54))
      | ~ r2_hidden(A_53,k1_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_240,plain,(
    ! [A_100,C_101] :
      ( r2_hidden(k4_tarski('#skF_4'(A_100,k2_relat_1(A_100),C_101),C_101),A_100)
      | ~ r2_hidden(C_101,k2_relat_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_260,plain,(
    ! [C_105] : ~ r2_hidden(C_105,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_240,c_97])).

tff(c_272,plain,(
    ! [A_53] :
      ( ~ r2_hidden(A_53,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_46,c_260])).

tff(c_277,plain,(
    ! [A_53] : ~ r2_hidden(A_53,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_272])).

tff(c_496,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_449,c_277])).

tff(c_521,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_496])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_521])).

tff(c_523,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_853,plain,(
    ! [A_180,B_181] :
      ( r2_hidden(k4_tarski('#skF_2'(A_180,B_181),'#skF_1'(A_180,B_181)),A_180)
      | r2_hidden('#skF_3'(A_180,B_181),B_181)
      | k2_relat_1(A_180) = B_181 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_529,plain,(
    ! [C_122,B_123] : ~ r2_hidden(C_122,k4_xboole_0(B_123,k1_tarski(C_122))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_532,plain,(
    ! [C_122] : ~ r2_hidden(C_122,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_529])).

tff(c_913,plain,(
    ! [B_182] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_182),B_182)
      | k2_relat_1(k1_xboole_0) = B_182 ) ),
    inference(resolution,[status(thm)],[c_853,c_532])).

tff(c_957,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_913,c_532])).

tff(c_972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_523,c_957])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:07:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.46  
% 2.67/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.46  %$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1 > #skF_5
% 2.67/1.46  
% 2.67/1.46  %Foreground sorts:
% 2.67/1.46  
% 2.67/1.46  
% 2.67/1.46  %Background operators:
% 2.67/1.46  
% 2.67/1.46  
% 2.67/1.46  %Foreground operators:
% 2.67/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.67/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.67/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.67/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.67/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.46  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.67/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.67/1.46  
% 2.96/1.47  tff(f_79, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.96/1.47  tff(f_64, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.96/1.47  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.96/1.47  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.96/1.47  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.96/1.47  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.96/1.47  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 2.96/1.47  tff(c_48, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.96/1.47  tff(c_93, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.96/1.47  tff(c_394, plain, (![A_119, B_120]: (r2_hidden(k4_tarski('#skF_2'(A_119, B_120), '#skF_1'(A_119, B_120)), A_119) | r2_hidden('#skF_3'(A_119, B_120), B_120) | k2_relat_1(A_119)=B_120)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.96/1.47  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.47  tff(c_94, plain, (![C_62, B_63]: (~r2_hidden(C_62, k4_xboole_0(B_63, k1_tarski(C_62))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.96/1.47  tff(c_97, plain, (![C_62]: (~r2_hidden(C_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_94])).
% 2.96/1.47  tff(c_449, plain, (![B_121]: (r2_hidden('#skF_3'(k1_xboole_0, B_121), B_121) | k2_relat_1(k1_xboole_0)=B_121)), inference(resolution, [status(thm)], [c_394, c_97])).
% 2.96/1.47  tff(c_500, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_449, c_97])).
% 2.96/1.47  tff(c_57, plain, (![B_59]: (k2_zfmisc_1(k1_xboole_0, B_59)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.47  tff(c_44, plain, (![A_51, B_52]: (v1_relat_1(k2_zfmisc_1(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.96/1.47  tff(c_61, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_57, c_44])).
% 2.96/1.47  tff(c_46, plain, (![A_53, B_54]: (r2_hidden('#skF_5'(A_53, B_54), k2_relat_1(B_54)) | ~r2_hidden(A_53, k1_relat_1(B_54)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.96/1.47  tff(c_240, plain, (![A_100, C_101]: (r2_hidden(k4_tarski('#skF_4'(A_100, k2_relat_1(A_100), C_101), C_101), A_100) | ~r2_hidden(C_101, k2_relat_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.96/1.47  tff(c_260, plain, (![C_105]: (~r2_hidden(C_105, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_240, c_97])).
% 2.96/1.47  tff(c_272, plain, (![A_53]: (~r2_hidden(A_53, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_260])).
% 2.96/1.47  tff(c_277, plain, (![A_53]: (~r2_hidden(A_53, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_272])).
% 2.96/1.47  tff(c_496, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_449, c_277])).
% 2.96/1.47  tff(c_521, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_500, c_496])).
% 2.96/1.47  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_521])).
% 2.96/1.47  tff(c_523, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.96/1.47  tff(c_853, plain, (![A_180, B_181]: (r2_hidden(k4_tarski('#skF_2'(A_180, B_181), '#skF_1'(A_180, B_181)), A_180) | r2_hidden('#skF_3'(A_180, B_181), B_181) | k2_relat_1(A_180)=B_181)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.96/1.47  tff(c_529, plain, (![C_122, B_123]: (~r2_hidden(C_122, k4_xboole_0(B_123, k1_tarski(C_122))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.96/1.47  tff(c_532, plain, (![C_122]: (~r2_hidden(C_122, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_529])).
% 2.96/1.47  tff(c_913, plain, (![B_182]: (r2_hidden('#skF_3'(k1_xboole_0, B_182), B_182) | k2_relat_1(k1_xboole_0)=B_182)), inference(resolution, [status(thm)], [c_853, c_532])).
% 2.96/1.47  tff(c_957, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_913, c_532])).
% 2.96/1.47  tff(c_972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_523, c_957])).
% 2.96/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.47  
% 2.96/1.47  Inference rules
% 2.96/1.47  ----------------------
% 2.96/1.47  #Ref     : 0
% 2.96/1.47  #Sup     : 186
% 2.96/1.47  #Fact    : 0
% 2.96/1.47  #Define  : 0
% 2.96/1.47  #Split   : 4
% 2.96/1.47  #Chain   : 0
% 2.96/1.47  #Close   : 0
% 2.96/1.47  
% 2.96/1.47  Ordering : KBO
% 2.96/1.47  
% 2.96/1.47  Simplification rules
% 2.96/1.47  ----------------------
% 2.96/1.47  #Subsume      : 30
% 2.96/1.47  #Demod        : 20
% 2.96/1.47  #Tautology    : 69
% 2.96/1.47  #SimpNegUnit  : 8
% 2.96/1.47  #BackRed      : 5
% 2.96/1.47  
% 2.96/1.47  #Partial instantiations: 0
% 2.96/1.47  #Strategies tried      : 1
% 2.96/1.47  
% 2.96/1.47  Timing (in seconds)
% 2.96/1.47  ----------------------
% 2.96/1.47  Preprocessing        : 0.34
% 2.96/1.47  Parsing              : 0.18
% 2.96/1.47  CNF conversion       : 0.02
% 2.96/1.47  Main loop            : 0.34
% 2.96/1.47  Inferencing          : 0.14
% 2.96/1.47  Reduction            : 0.10
% 2.96/1.47  Demodulation         : 0.06
% 2.96/1.47  BG Simplification    : 0.02
% 2.96/1.47  Subsumption          : 0.06
% 2.96/1.47  Abstraction          : 0.02
% 2.96/1.47  MUC search           : 0.00
% 2.96/1.47  Cooper               : 0.00
% 2.96/1.47  Total                : 0.71
% 2.96/1.47  Index Insertion      : 0.00
% 2.96/1.47  Index Deletion       : 0.00
% 2.96/1.47  Index Matching       : 0.00
% 2.96/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
