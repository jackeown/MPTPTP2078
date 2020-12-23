%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:17 EST 2020

% Result     : Theorem 21.77s
% Output     : CNFRefutation 22.08s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 100 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 205 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_81,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_62,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38598,plain,(
    ! [A_2772,B_2773] :
      ( r1_ordinal1(A_2772,B_2773)
      | ~ r1_tarski(A_2772,B_2773)
      | ~ v3_ordinal1(B_2773)
      | ~ v3_ordinal1(A_2772) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_38607,plain,(
    ! [B_2774] :
      ( r1_ordinal1(B_2774,B_2774)
      | ~ v3_ordinal1(B_2774) ) ),
    inference(resolution,[status(thm)],[c_26,c_38598])).

tff(c_56,plain,(
    ! [B_22] : r2_hidden(B_22,k1_ordinal1(B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_64,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_66,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_128,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_72])).

tff(c_660,plain,(
    ! [B_105,A_106] :
      ( r2_hidden(B_105,A_106)
      | r1_ordinal1(A_106,B_105)
      | ~ v3_ordinal1(B_105)
      | ~ v3_ordinal1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_129,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden(A_44,B_45)
      | r2_hidden(A_44,k1_ordinal1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_156,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_129,c_95])).

tff(c_763,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_660,c_156])).

tff(c_813,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_763])).

tff(c_52,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ r1_ordinal1(A_19,B_20)
      | ~ v3_ordinal1(B_20)
      | ~ v3_ordinal1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_904,plain,(
    ! [A_117,B_118] :
      ( r1_tarski(A_117,B_118)
      | ~ r1_ordinal1(A_117,B_118)
      | ~ v3_ordinal1(B_118)
      | ~ v3_ordinal1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3746,plain,(
    ! [B_327,A_328] :
      ( B_327 = A_328
      | ~ r1_tarski(B_327,A_328)
      | ~ r1_ordinal1(A_328,B_327)
      | ~ v3_ordinal1(B_327)
      | ~ v3_ordinal1(A_328) ) ),
    inference(resolution,[status(thm)],[c_904,c_22])).

tff(c_37655,plain,(
    ! [B_2672,A_2673] :
      ( B_2672 = A_2673
      | ~ r1_ordinal1(B_2672,A_2673)
      | ~ r1_ordinal1(A_2673,B_2672)
      | ~ v3_ordinal1(B_2672)
      | ~ v3_ordinal1(A_2673) ) ),
    inference(resolution,[status(thm)],[c_52,c_3746])).

tff(c_37691,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_813,c_37655])).

tff(c_37714,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_128,c_37691])).

tff(c_37721,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37714,c_95])).

tff(c_37725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_37721])).

tff(c_37726,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_38262,plain,(
    ! [B_2742,A_2743] :
      ( r2_hidden(B_2742,A_2743)
      | r1_ordinal1(A_2743,B_2742)
      | ~ v3_ordinal1(B_2742)
      | ~ v3_ordinal1(A_2743) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_37727,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_38091,plain,(
    ! [B_2716,A_2717] :
      ( B_2716 = A_2717
      | r2_hidden(A_2717,B_2716)
      | ~ r2_hidden(A_2717,k1_ordinal1(B_2716)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38102,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_37727,c_38091])).

tff(c_38105,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_38102])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_38108,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_38105,c_2])).

tff(c_38299,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38262,c_38108])).

tff(c_38390,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_38299])).

tff(c_38392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37726,c_38390])).

tff(c_38393,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38102])).

tff(c_38397,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38393,c_37726])).

tff(c_38610,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38607,c_38397])).

tff(c_38614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38610])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.77/11.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.77/11.65  
% 21.77/11.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.77/11.65  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 21.77/11.65  
% 21.77/11.65  %Foreground sorts:
% 21.77/11.65  
% 21.77/11.65  
% 21.77/11.65  %Background operators:
% 21.77/11.65  
% 21.77/11.65  
% 21.77/11.65  %Foreground operators:
% 21.77/11.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 21.77/11.65  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 21.77/11.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.77/11.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.77/11.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 21.77/11.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 21.77/11.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.77/11.65  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 21.77/11.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.77/11.65  tff('#skF_5', type, '#skF_5': $i).
% 21.77/11.65  tff('#skF_6', type, '#skF_6': $i).
% 21.77/11.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 21.77/11.65  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 21.77/11.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.77/11.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 21.77/11.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.77/11.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.77/11.65  
% 22.08/11.66  tff(f_91, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 22.08/11.66  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.08/11.66  tff(f_66, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 22.08/11.66  tff(f_72, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 22.08/11.66  tff(f_81, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 22.08/11.66  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 22.08/11.66  tff(c_62, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 22.08/11.66  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.08/11.66  tff(c_38598, plain, (![A_2772, B_2773]: (r1_ordinal1(A_2772, B_2773) | ~r1_tarski(A_2772, B_2773) | ~v3_ordinal1(B_2773) | ~v3_ordinal1(A_2772))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.08/11.66  tff(c_38607, plain, (![B_2774]: (r1_ordinal1(B_2774, B_2774) | ~v3_ordinal1(B_2774))), inference(resolution, [status(thm)], [c_26, c_38598])).
% 22.08/11.66  tff(c_56, plain, (![B_22]: (r2_hidden(B_22, k1_ordinal1(B_22)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.08/11.66  tff(c_64, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 22.08/11.66  tff(c_66, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 22.08/11.66  tff(c_95, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_66])).
% 22.08/11.66  tff(c_72, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 22.08/11.66  tff(c_128, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_95, c_72])).
% 22.08/11.66  tff(c_660, plain, (![B_105, A_106]: (r2_hidden(B_105, A_106) | r1_ordinal1(A_106, B_105) | ~v3_ordinal1(B_105) | ~v3_ordinal1(A_106))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.08/11.66  tff(c_129, plain, (![A_44, B_45]: (~r2_hidden(A_44, B_45) | r2_hidden(A_44, k1_ordinal1(B_45)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.08/11.66  tff(c_156, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_129, c_95])).
% 22.08/11.66  tff(c_763, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_660, c_156])).
% 22.08/11.66  tff(c_813, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_763])).
% 22.08/11.66  tff(c_52, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~r1_ordinal1(A_19, B_20) | ~v3_ordinal1(B_20) | ~v3_ordinal1(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.08/11.66  tff(c_904, plain, (![A_117, B_118]: (r1_tarski(A_117, B_118) | ~r1_ordinal1(A_117, B_118) | ~v3_ordinal1(B_118) | ~v3_ordinal1(A_117))), inference(cnfTransformation, [status(thm)], [f_66])).
% 22.08/11.66  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.08/11.66  tff(c_3746, plain, (![B_327, A_328]: (B_327=A_328 | ~r1_tarski(B_327, A_328) | ~r1_ordinal1(A_328, B_327) | ~v3_ordinal1(B_327) | ~v3_ordinal1(A_328))), inference(resolution, [status(thm)], [c_904, c_22])).
% 22.08/11.66  tff(c_37655, plain, (![B_2672, A_2673]: (B_2672=A_2673 | ~r1_ordinal1(B_2672, A_2673) | ~r1_ordinal1(A_2673, B_2672) | ~v3_ordinal1(B_2672) | ~v3_ordinal1(A_2673))), inference(resolution, [status(thm)], [c_52, c_3746])).
% 22.08/11.66  tff(c_37691, plain, ('#skF_5'='#skF_6' | ~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_813, c_37655])).
% 22.08/11.66  tff(c_37714, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_128, c_37691])).
% 22.08/11.66  tff(c_37721, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_37714, c_95])).
% 22.08/11.66  tff(c_37725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_37721])).
% 22.08/11.66  tff(c_37726, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_66])).
% 22.08/11.66  tff(c_38262, plain, (![B_2742, A_2743]: (r2_hidden(B_2742, A_2743) | r1_ordinal1(A_2743, B_2742) | ~v3_ordinal1(B_2742) | ~v3_ordinal1(A_2743))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.08/11.66  tff(c_37727, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_66])).
% 22.08/11.66  tff(c_38091, plain, (![B_2716, A_2717]: (B_2716=A_2717 | r2_hidden(A_2717, B_2716) | ~r2_hidden(A_2717, k1_ordinal1(B_2716)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.08/11.66  tff(c_38102, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_37727, c_38091])).
% 22.08/11.66  tff(c_38105, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_38102])).
% 22.08/11.66  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 22.08/11.66  tff(c_38108, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_38105, c_2])).
% 22.08/11.66  tff(c_38299, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_38262, c_38108])).
% 22.08/11.66  tff(c_38390, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_38299])).
% 22.08/11.66  tff(c_38392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37726, c_38390])).
% 22.08/11.66  tff(c_38393, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_38102])).
% 22.08/11.66  tff(c_38397, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38393, c_37726])).
% 22.08/11.66  tff(c_38610, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_38607, c_38397])).
% 22.08/11.66  tff(c_38614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_38610])).
% 22.08/11.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.08/11.66  
% 22.08/11.66  Inference rules
% 22.08/11.66  ----------------------
% 22.08/11.66  #Ref     : 0
% 22.08/11.66  #Sup     : 8222
% 22.08/11.66  #Fact    : 52
% 22.08/11.66  #Define  : 0
% 22.08/11.66  #Split   : 3
% 22.08/11.66  #Chain   : 0
% 22.08/11.66  #Close   : 0
% 22.08/11.66  
% 22.08/11.66  Ordering : KBO
% 22.08/11.66  
% 22.08/11.66  Simplification rules
% 22.08/11.66  ----------------------
% 22.12/11.66  #Subsume      : 2990
% 22.12/11.66  #Demod        : 750
% 22.12/11.66  #Tautology    : 314
% 22.12/11.66  #SimpNegUnit  : 177
% 22.12/11.66  #BackRed      : 11
% 22.12/11.66  
% 22.12/11.66  #Partial instantiations: 0
% 22.12/11.66  #Strategies tried      : 1
% 22.12/11.66  
% 22.12/11.66  Timing (in seconds)
% 22.12/11.66  ----------------------
% 22.12/11.67  Preprocessing        : 0.34
% 22.12/11.67  Parsing              : 0.17
% 22.12/11.67  CNF conversion       : 0.03
% 22.12/11.67  Main loop            : 10.51
% 22.12/11.67  Inferencing          : 1.38
% 22.12/11.67  Reduction            : 3.53
% 22.12/11.67  Demodulation         : 1.08
% 22.12/11.67  BG Simplification    : 0.14
% 22.12/11.67  Subsumption          : 4.87
% 22.12/11.67  Abstraction          : 0.19
% 22.12/11.67  MUC search           : 0.00
% 22.12/11.67  Cooper               : 0.00
% 22.12/11.67  Total                : 10.88
% 22.12/11.67  Index Insertion      : 0.00
% 22.12/11.67  Index Deletion       : 0.00
% 22.12/11.67  Index Matching       : 0.00
% 22.12/11.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
