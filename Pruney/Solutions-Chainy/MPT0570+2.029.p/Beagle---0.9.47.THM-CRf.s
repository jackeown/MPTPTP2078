%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:45 EST 2020

% Result     : Theorem 12.11s
% Output     : CNFRefutation 12.18s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 204 expanded)
%              Number of leaves         :   25 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 465 expanded)
%              Number of equality atoms :   27 (  97 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_64,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_420,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r2_hidden('#skF_2'(A_87,B_88,C_89),C_89)
      | r2_hidden('#skF_3'(A_87,B_88,C_89),C_89)
      | k4_xboole_0(A_87,B_88) = C_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_429,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,A_6),A_6)
      | k4_xboole_0(A_6,B_7) = A_6 ) ),
    inference(resolution,[status(thm)],[c_24,c_420])).

tff(c_18,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_657,plain,(
    ! [A_114,B_115,C_116] :
      ( ~ r2_hidden('#skF_2'(A_114,B_115,C_116),C_116)
      | r2_hidden('#skF_3'(A_114,B_115,C_116),B_115)
      | ~ r2_hidden('#skF_3'(A_114,B_115,C_116),A_114)
      | k4_xboole_0(A_114,B_115) = C_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3009,plain,(
    ! [A_299,B_300] :
      ( r2_hidden('#skF_3'(A_299,B_300,A_299),B_300)
      | ~ r2_hidden('#skF_3'(A_299,B_300,A_299),A_299)
      | k4_xboole_0(A_299,B_300) = A_299 ) ),
    inference(resolution,[status(thm)],[c_18,c_657])).

tff(c_3043,plain,(
    ! [A_301,B_302] :
      ( r2_hidden('#skF_3'(A_301,B_302,A_301),B_302)
      | k4_xboole_0(A_301,B_302) = A_301 ) ),
    inference(resolution,[status(thm)],[c_429,c_3009])).

tff(c_34,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_61,plain,(
    ! [A_26,C_27,B_28] :
      ( ~ r2_hidden(A_26,C_27)
      | ~ r1_xboole_0(k2_tarski(A_26,B_28),C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_66,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_3100,plain,(
    ! [A_301] : k4_xboole_0(A_301,k1_xboole_0) = A_301 ),
    inference(resolution,[status(thm)],[c_3043,c_66])).

tff(c_44,plain,(
    r1_tarski('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_269,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden('#skF_2'(A_74,B_75,C_76),A_74)
      | r2_hidden('#skF_3'(A_74,B_75,C_76),C_76)
      | k4_xboole_0(A_74,B_75) = C_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3944,plain,(
    ! [A_316,B_317,C_318,B_319] :
      ( r2_hidden('#skF_2'(A_316,B_317,C_318),B_319)
      | ~ r1_tarski(A_316,B_319)
      | r2_hidden('#skF_3'(A_316,B_317,C_318),C_318)
      | k4_xboole_0(A_316,B_317) = C_318 ) ),
    inference(resolution,[status(thm)],[c_269,c_2])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8303,plain,(
    ! [A_497,B_498,C_499] :
      ( ~ r1_tarski(A_497,B_498)
      | r2_hidden('#skF_3'(A_497,B_498,C_499),C_499)
      | k4_xboole_0(A_497,B_498) = C_499 ) ),
    inference(resolution,[status(thm)],[c_3944,c_22])).

tff(c_8379,plain,(
    ! [A_500,B_501] :
      ( ~ r1_tarski(A_500,B_501)
      | k4_xboole_0(A_500,B_501) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8303,c_66])).

tff(c_8425,plain,(
    k4_xboole_0('#skF_5',k2_relat_1('#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_8379])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [D_58,A_59,B_60] :
      ( r2_hidden(D_58,k4_xboole_0(A_59,B_60))
      | r2_hidden(D_58,B_60)
      | ~ r2_hidden(D_58,A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4584,plain,(
    ! [A_341,A_342,B_343] :
      ( r1_tarski(A_341,k4_xboole_0(A_342,B_343))
      | r2_hidden('#skF_1'(A_341,k4_xboole_0(A_342,B_343)),B_343)
      | ~ r2_hidden('#skF_1'(A_341,k4_xboole_0(A_342,B_343)),A_342) ) ),
    inference(resolution,[status(thm)],[c_175,c_4])).

tff(c_4619,plain,(
    ! [A_1,B_343] :
      ( r2_hidden('#skF_1'(A_1,k4_xboole_0(A_1,B_343)),B_343)
      | r1_tarski(A_1,k4_xboole_0(A_1,B_343)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4584])).

tff(c_8712,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_xboole_0),k2_relat_1('#skF_6'))
    | r1_tarski('#skF_5',k4_xboole_0('#skF_5',k2_relat_1('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8425,c_4619])).

tff(c_8890,plain,
    ( r2_hidden('#skF_1'('#skF_5',k1_xboole_0),k2_relat_1('#skF_6'))
    | r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8425,c_8712])).

tff(c_9572,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8890])).

tff(c_8378,plain,(
    ! [A_497,B_498] :
      ( ~ r1_tarski(A_497,B_498)
      | k4_xboole_0(A_497,B_498) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8303,c_66])).

tff(c_9575,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9572,c_8378])).

tff(c_9599,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3100,c_9575])).

tff(c_9601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_9599])).

tff(c_9603,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8890])).

tff(c_48,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9602,plain,(
    r2_hidden('#skF_1'('#skF_5',k1_xboole_0),k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_8890])).

tff(c_152,plain,(
    ! [B_53,A_54] :
      ( r1_xboole_0(k2_relat_1(B_53),A_54)
      | k10_relat_1(B_53,A_54) != k1_xboole_0
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,B_13)
      | ~ r2_hidden(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2387,plain,(
    ! [C_258,A_259,B_260] :
      ( ~ r2_hidden(C_258,A_259)
      | ~ r2_hidden(C_258,k2_relat_1(B_260))
      | k10_relat_1(B_260,A_259) != k1_xboole_0
      | ~ v1_relat_1(B_260) ) ),
    inference(resolution,[status(thm)],[c_152,c_26])).

tff(c_30080,plain,(
    ! [A_871,B_872,B_873] :
      ( ~ r2_hidden('#skF_1'(A_871,B_872),k2_relat_1(B_873))
      | k10_relat_1(B_873,A_871) != k1_xboole_0
      | ~ v1_relat_1(B_873)
      | r1_tarski(A_871,B_872) ) ),
    inference(resolution,[status(thm)],[c_6,c_2387])).

tff(c_30090,plain,
    ( k10_relat_1('#skF_6','#skF_5') != k1_xboole_0
    | ~ v1_relat_1('#skF_6')
    | r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9602,c_30080])).

tff(c_30119,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_30090])).

tff(c_30121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9603,c_30119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:34:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.11/4.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.11/4.95  
% 12.11/4.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.11/4.95  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.11/4.95  
% 12.11/4.95  %Foreground sorts:
% 12.11/4.95  
% 12.11/4.95  
% 12.11/4.95  %Background operators:
% 12.11/4.95  
% 12.11/4.95  
% 12.11/4.95  %Foreground operators:
% 12.11/4.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.11/4.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.11/4.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.11/4.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.11/4.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.11/4.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.11/4.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.11/4.95  tff('#skF_5', type, '#skF_5': $i).
% 12.11/4.95  tff('#skF_6', type, '#skF_6': $i).
% 12.11/4.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.11/4.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.11/4.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.11/4.95  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.11/4.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.11/4.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.11/4.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.11/4.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.11/4.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.11/4.95  
% 12.18/4.96  tff(f_86, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 12.18/4.96  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.18/4.96  tff(f_64, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 12.18/4.96  tff(f_69, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 12.18/4.96  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 12.18/4.96  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 12.18/4.96  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 12.18/4.96  tff(c_46, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.18/4.96  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.18/4.96  tff(c_420, plain, (![A_87, B_88, C_89]: (~r2_hidden('#skF_2'(A_87, B_88, C_89), C_89) | r2_hidden('#skF_3'(A_87, B_88, C_89), C_89) | k4_xboole_0(A_87, B_88)=C_89)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.18/4.96  tff(c_429, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, A_6), A_6) | k4_xboole_0(A_6, B_7)=A_6)), inference(resolution, [status(thm)], [c_24, c_420])).
% 12.18/4.96  tff(c_18, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), B_7) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.18/4.96  tff(c_657, plain, (![A_114, B_115, C_116]: (~r2_hidden('#skF_2'(A_114, B_115, C_116), C_116) | r2_hidden('#skF_3'(A_114, B_115, C_116), B_115) | ~r2_hidden('#skF_3'(A_114, B_115, C_116), A_114) | k4_xboole_0(A_114, B_115)=C_116)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.18/4.96  tff(c_3009, plain, (![A_299, B_300]: (r2_hidden('#skF_3'(A_299, B_300, A_299), B_300) | ~r2_hidden('#skF_3'(A_299, B_300, A_299), A_299) | k4_xboole_0(A_299, B_300)=A_299)), inference(resolution, [status(thm)], [c_18, c_657])).
% 12.18/4.96  tff(c_3043, plain, (![A_301, B_302]: (r2_hidden('#skF_3'(A_301, B_302, A_301), B_302) | k4_xboole_0(A_301, B_302)=A_301)), inference(resolution, [status(thm)], [c_429, c_3009])).
% 12.18/4.96  tff(c_34, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.18/4.96  tff(c_61, plain, (![A_26, C_27, B_28]: (~r2_hidden(A_26, C_27) | ~r1_xboole_0(k2_tarski(A_26, B_28), C_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.18/4.96  tff(c_66, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_61])).
% 12.18/4.96  tff(c_3100, plain, (![A_301]: (k4_xboole_0(A_301, k1_xboole_0)=A_301)), inference(resolution, [status(thm)], [c_3043, c_66])).
% 12.18/4.96  tff(c_44, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.18/4.96  tff(c_269, plain, (![A_74, B_75, C_76]: (r2_hidden('#skF_2'(A_74, B_75, C_76), A_74) | r2_hidden('#skF_3'(A_74, B_75, C_76), C_76) | k4_xboole_0(A_74, B_75)=C_76)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.18/4.96  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.18/4.96  tff(c_3944, plain, (![A_316, B_317, C_318, B_319]: (r2_hidden('#skF_2'(A_316, B_317, C_318), B_319) | ~r1_tarski(A_316, B_319) | r2_hidden('#skF_3'(A_316, B_317, C_318), C_318) | k4_xboole_0(A_316, B_317)=C_318)), inference(resolution, [status(thm)], [c_269, c_2])).
% 12.18/4.96  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.18/4.96  tff(c_8303, plain, (![A_497, B_498, C_499]: (~r1_tarski(A_497, B_498) | r2_hidden('#skF_3'(A_497, B_498, C_499), C_499) | k4_xboole_0(A_497, B_498)=C_499)), inference(resolution, [status(thm)], [c_3944, c_22])).
% 12.18/4.96  tff(c_8379, plain, (![A_500, B_501]: (~r1_tarski(A_500, B_501) | k4_xboole_0(A_500, B_501)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8303, c_66])).
% 12.18/4.96  tff(c_8425, plain, (k4_xboole_0('#skF_5', k2_relat_1('#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_8379])).
% 12.18/4.96  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.18/4.96  tff(c_175, plain, (![D_58, A_59, B_60]: (r2_hidden(D_58, k4_xboole_0(A_59, B_60)) | r2_hidden(D_58, B_60) | ~r2_hidden(D_58, A_59))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.18/4.96  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.18/4.96  tff(c_4584, plain, (![A_341, A_342, B_343]: (r1_tarski(A_341, k4_xboole_0(A_342, B_343)) | r2_hidden('#skF_1'(A_341, k4_xboole_0(A_342, B_343)), B_343) | ~r2_hidden('#skF_1'(A_341, k4_xboole_0(A_342, B_343)), A_342))), inference(resolution, [status(thm)], [c_175, c_4])).
% 12.18/4.96  tff(c_4619, plain, (![A_1, B_343]: (r2_hidden('#skF_1'(A_1, k4_xboole_0(A_1, B_343)), B_343) | r1_tarski(A_1, k4_xboole_0(A_1, B_343)))), inference(resolution, [status(thm)], [c_6, c_4584])).
% 12.18/4.96  tff(c_8712, plain, (r2_hidden('#skF_1'('#skF_5', k1_xboole_0), k2_relat_1('#skF_6')) | r1_tarski('#skF_5', k4_xboole_0('#skF_5', k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8425, c_4619])).
% 12.18/4.96  tff(c_8890, plain, (r2_hidden('#skF_1'('#skF_5', k1_xboole_0), k2_relat_1('#skF_6')) | r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8425, c_8712])).
% 12.18/4.96  tff(c_9572, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8890])).
% 12.18/4.96  tff(c_8378, plain, (![A_497, B_498]: (~r1_tarski(A_497, B_498) | k4_xboole_0(A_497, B_498)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8303, c_66])).
% 12.18/4.96  tff(c_9575, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_9572, c_8378])).
% 12.18/4.96  tff(c_9599, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3100, c_9575])).
% 12.18/4.96  tff(c_9601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_9599])).
% 12.18/4.96  tff(c_9603, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8890])).
% 12.18/4.96  tff(c_48, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.18/4.96  tff(c_42, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 12.18/4.96  tff(c_9602, plain, (r2_hidden('#skF_1'('#skF_5', k1_xboole_0), k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_8890])).
% 12.18/4.96  tff(c_152, plain, (![B_53, A_54]: (r1_xboole_0(k2_relat_1(B_53), A_54) | k10_relat_1(B_53, A_54)!=k1_xboole_0 | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.18/4.96  tff(c_26, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, B_13) | ~r2_hidden(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.18/4.96  tff(c_2387, plain, (![C_258, A_259, B_260]: (~r2_hidden(C_258, A_259) | ~r2_hidden(C_258, k2_relat_1(B_260)) | k10_relat_1(B_260, A_259)!=k1_xboole_0 | ~v1_relat_1(B_260))), inference(resolution, [status(thm)], [c_152, c_26])).
% 12.18/4.96  tff(c_30080, plain, (![A_871, B_872, B_873]: (~r2_hidden('#skF_1'(A_871, B_872), k2_relat_1(B_873)) | k10_relat_1(B_873, A_871)!=k1_xboole_0 | ~v1_relat_1(B_873) | r1_tarski(A_871, B_872))), inference(resolution, [status(thm)], [c_6, c_2387])).
% 12.18/4.96  tff(c_30090, plain, (k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0 | ~v1_relat_1('#skF_6') | r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_9602, c_30080])).
% 12.18/4.96  tff(c_30119, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_30090])).
% 12.18/4.96  tff(c_30121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9603, c_30119])).
% 12.18/4.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.18/4.96  
% 12.18/4.96  Inference rules
% 12.18/4.96  ----------------------
% 12.18/4.96  #Ref     : 0
% 12.18/4.96  #Sup     : 7832
% 12.18/4.96  #Fact    : 0
% 12.18/4.96  #Define  : 0
% 12.18/4.96  #Split   : 3
% 12.18/4.96  #Chain   : 0
% 12.18/4.96  #Close   : 0
% 12.18/4.96  
% 12.18/4.96  Ordering : KBO
% 12.18/4.96  
% 12.18/4.96  Simplification rules
% 12.18/4.96  ----------------------
% 12.18/4.96  #Subsume      : 3754
% 12.18/4.96  #Demod        : 3779
% 12.18/4.96  #Tautology    : 1850
% 12.18/4.96  #SimpNegUnit  : 144
% 12.18/4.96  #BackRed      : 1
% 12.18/4.96  
% 12.18/4.96  #Partial instantiations: 0
% 12.18/4.96  #Strategies tried      : 1
% 12.18/4.96  
% 12.18/4.96  Timing (in seconds)
% 12.18/4.96  ----------------------
% 12.18/4.97  Preprocessing        : 0.32
% 12.18/4.97  Parsing              : 0.17
% 12.18/4.97  CNF conversion       : 0.02
% 12.18/4.97  Main loop            : 3.82
% 12.18/4.97  Inferencing          : 0.86
% 12.18/4.97  Reduction            : 1.13
% 12.18/4.97  Demodulation         : 0.82
% 12.18/4.97  BG Simplification    : 0.08
% 12.18/4.97  Subsumption          : 1.53
% 12.18/4.97  Abstraction          : 0.13
% 12.18/4.97  MUC search           : 0.00
% 12.18/4.97  Cooper               : 0.00
% 12.18/4.97  Total                : 4.17
% 12.18/4.97  Index Insertion      : 0.00
% 12.18/4.97  Index Deletion       : 0.00
% 12.18/4.97  Index Matching       : 0.00
% 12.18/4.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
