%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:26 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   58 (  66 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 (  88 expanded)
%              Number of equality atoms :   15 (  17 expanded)
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

tff(f_98,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_60,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_118,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_109])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_64,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_175,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(A_88,B_87)
      | ~ v1_zfmisc_1(B_87)
      | v1_xboole_0(B_87)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_360,plain,(
    ! [A_114,B_115] :
      ( k3_xboole_0(A_114,B_115) = A_114
      | ~ v1_zfmisc_1(A_114)
      | v1_xboole_0(A_114)
      | v1_xboole_0(k3_xboole_0(A_114,B_115)) ) ),
    inference(resolution,[status(thm)],[c_38,c_175])).

tff(c_62,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_363,plain,
    ( k3_xboole_0('#skF_6','#skF_7') = '#skF_6'
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_360,c_62])).

tff(c_369,plain,
    ( k3_xboole_0('#skF_6','#skF_7') = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_363])).

tff(c_370,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_369])).

tff(c_36,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_388,plain,(
    k5_xboole_0('#skF_6','#skF_6') = k4_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_36])).

tff(c_397,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k4_xboole_0('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_388])).

tff(c_8,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,k4_xboole_0(A_6,B_7))
      | r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_444,plain,(
    ! [D_122] :
      ( r2_hidden(D_122,k4_xboole_0('#skF_6','#skF_6'))
      | r2_hidden(D_122,'#skF_7')
      | ~ r2_hidden(D_122,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_8])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_474,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,'#skF_7')
      | ~ r2_hidden(D_123,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_444,c_10])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_492,plain,(
    ! [A_124] :
      ( r1_tarski(A_124,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_124,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_474,c_4])).

tff(c_500,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_492])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_500])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:37:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.33  
% 2.30/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.34  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.61/1.34  
% 2.61/1.34  %Foreground sorts:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Background operators:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Foreground operators:
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.61/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.61/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.61/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.61/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.61/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.61/1.34  
% 2.61/1.35  tff(f_98, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 2.61/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.61/1.35  tff(f_44, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.61/1.35  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.61/1.35  tff(f_55, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.61/1.35  tff(f_86, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.61/1.35  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.61/1.35  tff(c_60, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.61/1.35  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.35  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.61/1.35  tff(c_109, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.35  tff(c_118, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_26, c_109])).
% 2.61/1.35  tff(c_66, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.61/1.35  tff(c_64, plain, (v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.61/1.35  tff(c_38, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.35  tff(c_175, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(A_88, B_87) | ~v1_zfmisc_1(B_87) | v1_xboole_0(B_87) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.61/1.35  tff(c_360, plain, (![A_114, B_115]: (k3_xboole_0(A_114, B_115)=A_114 | ~v1_zfmisc_1(A_114) | v1_xboole_0(A_114) | v1_xboole_0(k3_xboole_0(A_114, B_115)))), inference(resolution, [status(thm)], [c_38, c_175])).
% 2.61/1.35  tff(c_62, plain, (~v1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.61/1.35  tff(c_363, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_360, c_62])).
% 2.61/1.35  tff(c_369, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_363])).
% 2.61/1.35  tff(c_370, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_66, c_369])).
% 2.61/1.35  tff(c_36, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.35  tff(c_388, plain, (k5_xboole_0('#skF_6', '#skF_6')=k4_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_370, c_36])).
% 2.61/1.35  tff(c_397, plain, (k4_xboole_0('#skF_6', '#skF_7')=k4_xboole_0('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_388])).
% 2.61/1.35  tff(c_8, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, k4_xboole_0(A_6, B_7)) | r2_hidden(D_11, B_7) | ~r2_hidden(D_11, A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.61/1.35  tff(c_444, plain, (![D_122]: (r2_hidden(D_122, k4_xboole_0('#skF_6', '#skF_6')) | r2_hidden(D_122, '#skF_7') | ~r2_hidden(D_122, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_397, c_8])).
% 2.61/1.35  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.61/1.35  tff(c_474, plain, (![D_123]: (r2_hidden(D_123, '#skF_7') | ~r2_hidden(D_123, '#skF_6'))), inference(resolution, [status(thm)], [c_444, c_10])).
% 2.61/1.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.35  tff(c_492, plain, (![A_124]: (r1_tarski(A_124, '#skF_7') | ~r2_hidden('#skF_1'(A_124, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_474, c_4])).
% 2.61/1.35  tff(c_500, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_492])).
% 2.61/1.35  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_500])).
% 2.61/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  Inference rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Ref     : 0
% 2.61/1.35  #Sup     : 95
% 2.61/1.35  #Fact    : 0
% 2.61/1.35  #Define  : 0
% 2.61/1.35  #Split   : 1
% 2.61/1.35  #Chain   : 0
% 2.61/1.35  #Close   : 0
% 2.61/1.35  
% 2.61/1.35  Ordering : KBO
% 2.61/1.35  
% 2.61/1.35  Simplification rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Subsume      : 6
% 2.61/1.35  #Demod        : 13
% 2.61/1.35  #Tautology    : 42
% 2.61/1.35  #SimpNegUnit  : 3
% 2.61/1.35  #BackRed      : 1
% 2.61/1.35  
% 2.61/1.35  #Partial instantiations: 0
% 2.61/1.35  #Strategies tried      : 1
% 2.61/1.35  
% 2.61/1.35  Timing (in seconds)
% 2.61/1.35  ----------------------
% 2.61/1.35  Preprocessing        : 0.33
% 2.61/1.35  Parsing              : 0.17
% 2.61/1.35  CNF conversion       : 0.02
% 2.61/1.35  Main loop            : 0.26
% 2.61/1.35  Inferencing          : 0.09
% 2.61/1.35  Reduction            : 0.07
% 2.61/1.35  Demodulation         : 0.05
% 2.61/1.35  BG Simplification    : 0.02
% 2.61/1.35  Subsumption          : 0.05
% 2.61/1.35  Abstraction          : 0.02
% 2.61/1.35  MUC search           : 0.00
% 2.61/1.35  Cooper               : 0.00
% 2.61/1.35  Total                : 0.62
% 2.61/1.35  Index Insertion      : 0.00
% 2.61/1.35  Index Deletion       : 0.00
% 2.61/1.35  Index Matching       : 0.00
% 2.61/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
