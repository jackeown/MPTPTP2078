%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:25 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   68 (  81 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 117 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_62,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1642,plain,(
    ! [A_227,B_228,C_229] :
      ( r2_hidden('#skF_2'(A_227,B_228,C_229),A_227)
      | r2_hidden('#skF_3'(A_227,B_228,C_229),C_229)
      | k4_xboole_0(A_227,B_228) = C_229 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1710,plain,(
    ! [A_230,C_231] :
      ( r2_hidden('#skF_3'(A_230,A_230,C_231),C_231)
      | k4_xboole_0(A_230,A_230) = C_231 ) ),
    inference(resolution,[status(thm)],[c_1642,c_22])).

tff(c_58,plain,(
    ! [B_54,A_53] :
      ( ~ r1_tarski(B_54,A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1744,plain,(
    ! [C_232,A_233] :
      ( ~ r1_tarski(C_232,'#skF_3'(A_233,A_233,C_232))
      | k4_xboole_0(A_233,A_233) = C_232 ) ),
    inference(resolution,[status(thm)],[c_1710,c_58])).

tff(c_1819,plain,(
    ! [A_233] : k4_xboole_0(A_233,A_233) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1744])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_116,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_125,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_116])).

tff(c_1822,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1819,c_125])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_66,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_169,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(A_94,B_93)
      | ~ v1_zfmisc_1(B_93)
      | v1_xboole_0(B_93)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2727,plain,(
    ! [A_310,B_311] :
      ( k3_xboole_0(A_310,B_311) = A_310
      | ~ v1_zfmisc_1(A_310)
      | v1_xboole_0(A_310)
      | v1_xboole_0(k3_xboole_0(A_310,B_311)) ) ),
    inference(resolution,[status(thm)],[c_38,c_169])).

tff(c_64,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2730,plain,
    ( k3_xboole_0('#skF_6','#skF_7') = '#skF_6'
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2727,c_64])).

tff(c_2739,plain,
    ( k3_xboole_0('#skF_6','#skF_7') = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2730])).

tff(c_2740,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2739])).

tff(c_36,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2750,plain,(
    k5_xboole_0('#skF_6','#skF_6') = k4_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2740,c_36])).

tff(c_2759,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_2750])).

tff(c_197,plain,(
    ! [D_99,A_100,B_101] :
      ( r2_hidden(D_99,k4_xboole_0(A_100,B_101))
      | r2_hidden(D_99,B_101)
      | ~ r2_hidden(D_99,A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_217,plain,(
    ! [A_100,B_101,D_99] :
      ( ~ r1_tarski(k4_xboole_0(A_100,B_101),D_99)
      | r2_hidden(D_99,B_101)
      | ~ r2_hidden(D_99,A_100) ) ),
    inference(resolution,[status(thm)],[c_197,c_58])).

tff(c_2778,plain,(
    ! [D_99] :
      ( ~ r1_tarski(k1_xboole_0,D_99)
      | r2_hidden(D_99,'#skF_7')
      | ~ r2_hidden(D_99,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2759,c_217])).

tff(c_2887,plain,(
    ! [D_313] :
      ( r2_hidden(D_313,'#skF_7')
      | ~ r2_hidden(D_313,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2778])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3143,plain,(
    ! [A_318] :
      ( r1_tarski(A_318,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_318,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2887,c_4])).

tff(c_3151,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_3143])).

tff(c_3156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_3151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.69  
% 4.04/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.69  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 4.04/1.69  
% 4.04/1.69  %Foreground sorts:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Background operators:
% 4.04/1.69  
% 4.04/1.69  
% 4.04/1.69  %Foreground operators:
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.04/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.04/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.04/1.69  tff('#skF_7', type, '#skF_7': $i).
% 4.04/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.04/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.04/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.04/1.69  tff('#skF_6', type, '#skF_6': $i).
% 4.04/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.04/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.04/1.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.04/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.69  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.04/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.04/1.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.04/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.04/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.04/1.69  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.04/1.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.04/1.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.04/1.69  
% 4.04/1.71  tff(f_103, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 4.04/1.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.04/1.71  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.04/1.71  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.04/1.71  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.04/1.71  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.04/1.71  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.04/1.71  tff(f_55, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.04/1.71  tff(f_91, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.04/1.71  tff(c_62, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.04/1.71  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.71  tff(c_40, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.04/1.71  tff(c_1642, plain, (![A_227, B_228, C_229]: (r2_hidden('#skF_2'(A_227, B_228, C_229), A_227) | r2_hidden('#skF_3'(A_227, B_228, C_229), C_229) | k4_xboole_0(A_227, B_228)=C_229)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.04/1.71  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.04/1.71  tff(c_1710, plain, (![A_230, C_231]: (r2_hidden('#skF_3'(A_230, A_230, C_231), C_231) | k4_xboole_0(A_230, A_230)=C_231)), inference(resolution, [status(thm)], [c_1642, c_22])).
% 4.04/1.71  tff(c_58, plain, (![B_54, A_53]: (~r1_tarski(B_54, A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.04/1.71  tff(c_1744, plain, (![C_232, A_233]: (~r1_tarski(C_232, '#skF_3'(A_233, A_233, C_232)) | k4_xboole_0(A_233, A_233)=C_232)), inference(resolution, [status(thm)], [c_1710, c_58])).
% 4.04/1.71  tff(c_1819, plain, (![A_233]: (k4_xboole_0(A_233, A_233)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_1744])).
% 4.04/1.71  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.04/1.71  tff(c_116, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.04/1.71  tff(c_125, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_26, c_116])).
% 4.04/1.71  tff(c_1822, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1819, c_125])).
% 4.04/1.71  tff(c_68, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.04/1.71  tff(c_66, plain, (v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.04/1.71  tff(c_38, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.04/1.71  tff(c_169, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(A_94, B_93) | ~v1_zfmisc_1(B_93) | v1_xboole_0(B_93) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.04/1.71  tff(c_2727, plain, (![A_310, B_311]: (k3_xboole_0(A_310, B_311)=A_310 | ~v1_zfmisc_1(A_310) | v1_xboole_0(A_310) | v1_xboole_0(k3_xboole_0(A_310, B_311)))), inference(resolution, [status(thm)], [c_38, c_169])).
% 4.04/1.71  tff(c_64, plain, (~v1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.04/1.71  tff(c_2730, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_2727, c_64])).
% 4.04/1.71  tff(c_2739, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2730])).
% 4.04/1.71  tff(c_2740, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_68, c_2739])).
% 4.04/1.71  tff(c_36, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.04/1.71  tff(c_2750, plain, (k5_xboole_0('#skF_6', '#skF_6')=k4_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2740, c_36])).
% 4.04/1.71  tff(c_2759, plain, (k4_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1822, c_2750])).
% 4.04/1.71  tff(c_197, plain, (![D_99, A_100, B_101]: (r2_hidden(D_99, k4_xboole_0(A_100, B_101)) | r2_hidden(D_99, B_101) | ~r2_hidden(D_99, A_100))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.04/1.71  tff(c_217, plain, (![A_100, B_101, D_99]: (~r1_tarski(k4_xboole_0(A_100, B_101), D_99) | r2_hidden(D_99, B_101) | ~r2_hidden(D_99, A_100))), inference(resolution, [status(thm)], [c_197, c_58])).
% 4.04/1.71  tff(c_2778, plain, (![D_99]: (~r1_tarski(k1_xboole_0, D_99) | r2_hidden(D_99, '#skF_7') | ~r2_hidden(D_99, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2759, c_217])).
% 4.04/1.71  tff(c_2887, plain, (![D_313]: (r2_hidden(D_313, '#skF_7') | ~r2_hidden(D_313, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2778])).
% 4.04/1.71  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.04/1.71  tff(c_3143, plain, (![A_318]: (r1_tarski(A_318, '#skF_7') | ~r2_hidden('#skF_1'(A_318, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_2887, c_4])).
% 4.04/1.71  tff(c_3151, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_3143])).
% 4.04/1.71  tff(c_3156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_3151])).
% 4.04/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.71  
% 4.04/1.71  Inference rules
% 4.04/1.71  ----------------------
% 4.04/1.71  #Ref     : 0
% 4.04/1.71  #Sup     : 631
% 4.04/1.71  #Fact    : 0
% 4.04/1.71  #Define  : 0
% 4.04/1.71  #Split   : 5
% 4.04/1.71  #Chain   : 0
% 4.04/1.71  #Close   : 0
% 4.04/1.71  
% 4.04/1.71  Ordering : KBO
% 4.04/1.71  
% 4.04/1.71  Simplification rules
% 4.04/1.71  ----------------------
% 4.04/1.71  #Subsume      : 84
% 4.04/1.71  #Demod        : 392
% 4.04/1.71  #Tautology    : 331
% 4.04/1.71  #SimpNegUnit  : 3
% 4.04/1.71  #BackRed      : 27
% 4.04/1.71  
% 4.04/1.71  #Partial instantiations: 0
% 4.04/1.71  #Strategies tried      : 1
% 4.04/1.71  
% 4.04/1.71  Timing (in seconds)
% 4.04/1.71  ----------------------
% 4.04/1.71  Preprocessing        : 0.34
% 4.04/1.71  Parsing              : 0.18
% 4.04/1.71  CNF conversion       : 0.03
% 4.04/1.71  Main loop            : 0.60
% 4.04/1.71  Inferencing          : 0.22
% 4.04/1.71  Reduction            : 0.18
% 4.04/1.71  Demodulation         : 0.13
% 4.04/1.71  BG Simplification    : 0.03
% 4.04/1.71  Subsumption          : 0.13
% 4.04/1.71  Abstraction          : 0.03
% 4.04/1.71  MUC search           : 0.00
% 4.04/1.71  Cooper               : 0.00
% 4.04/1.71  Total                : 0.97
% 4.04/1.71  Index Insertion      : 0.00
% 4.04/1.71  Index Deletion       : 0.00
% 4.04/1.71  Index Matching       : 0.00
% 4.04/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
