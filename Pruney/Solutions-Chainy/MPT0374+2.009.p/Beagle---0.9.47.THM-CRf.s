%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:00 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 120 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :   87 ( 238 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_81,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_88,plain,(
    ! [B_60,A_61] :
      ( v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,A_61)
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_103,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_105,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_52,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    ! [B_44,A_43] :
      ( r2_hidden(B_44,A_43)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(k2_tarski(A_38,B_39),C_40)
      | ~ r2_hidden(B_39,C_40)
      | ~ r2_hidden(A_38,C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_47] : ~ v1_xboole_0(k1_zfmisc_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [A_45] : k2_subset_1(A_45) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    ! [A_46] : m1_subset_1(k2_subset_1(A_46),k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_55,plain,(
    ! [A_46] : m1_subset_1(A_46,k1_zfmisc_1(A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_zfmisc_1(A_41),k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_159,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_293,plain,(
    ! [B_113,B_114,A_115] :
      ( r2_hidden(B_113,B_114)
      | ~ r1_tarski(A_115,B_114)
      | ~ m1_subset_1(B_113,A_115)
      | v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_36,c_159])).

tff(c_301,plain,(
    ! [B_113,B_42,A_41] :
      ( r2_hidden(B_113,k1_zfmisc_1(B_42))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_41))
      | v1_xboole_0(k1_zfmisc_1(A_41))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_32,c_293])).

tff(c_340,plain,(
    ! [B_122,B_123,A_124] :
      ( r2_hidden(B_122,k1_zfmisc_1(B_123))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_124))
      | ~ r1_tarski(A_124,B_123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_301])).

tff(c_369,plain,(
    ! [A_130,B_131] :
      ( r2_hidden(A_130,k1_zfmisc_1(B_131))
      | ~ r1_tarski(A_130,B_131) ) ),
    inference(resolution,[status(thm)],[c_55,c_340])).

tff(c_34,plain,(
    ! [B_44,A_43] :
      ( m1_subset_1(B_44,A_43)
      | ~ r2_hidden(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_378,plain,(
    ! [A_130,B_131] :
      ( m1_subset_1(A_130,k1_zfmisc_1(B_131))
      | v1_xboole_0(k1_zfmisc_1(B_131))
      | ~ r1_tarski(A_130,B_131) ) ),
    inference(resolution,[status(thm)],[c_369,c_34])).

tff(c_388,plain,(
    ! [A_132,B_133] :
      ( m1_subset_1(A_132,k1_zfmisc_1(B_133))
      | ~ r1_tarski(A_132,B_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_378])).

tff(c_48,plain,(
    ~ m1_subset_1(k2_tarski('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_406,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_388,c_48])).

tff(c_413,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_406])).

tff(c_415,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_418,plain,
    ( ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_415])).

tff(c_421,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_418])).

tff(c_423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_421])).

tff(c_424,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_428,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_424])).

tff(c_431,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_428])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_431])).

tff(c_435,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_442,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_435,c_12])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:20:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.38  
% 2.62/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.39  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.62/1.39  
% 2.62/1.39  %Foreground sorts:
% 2.62/1.39  
% 2.62/1.39  
% 2.62/1.39  %Background operators:
% 2.62/1.39  
% 2.62/1.39  
% 2.62/1.39  %Foreground operators:
% 2.62/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.62/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.62/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.62/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.62/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.62/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.62/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.39  
% 2.62/1.40  tff(f_95, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_subset_1)).
% 2.62/1.40  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.62/1.40  tff(f_60, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.62/1.40  tff(f_84, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.62/1.40  tff(f_79, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.62/1.40  tff(f_81, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.62/1.40  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.62/1.40  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.62/1.40  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.62/1.40  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.62/1.40  tff(c_54, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.62/1.40  tff(c_88, plain, (![B_60, A_61]: (v1_xboole_0(B_60) | ~m1_subset_1(B_60, A_61) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.62/1.40  tff(c_103, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_88])).
% 2.62/1.40  tff(c_105, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_103])).
% 2.62/1.40  tff(c_52, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.62/1.40  tff(c_36, plain, (![B_44, A_43]: (r2_hidden(B_44, A_43) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.62/1.40  tff(c_26, plain, (![A_38, B_39, C_40]: (r1_tarski(k2_tarski(A_38, B_39), C_40) | ~r2_hidden(B_39, C_40) | ~r2_hidden(A_38, C_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.62/1.40  tff(c_46, plain, (![A_47]: (~v1_xboole_0(k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.62/1.40  tff(c_42, plain, (![A_45]: (k2_subset_1(A_45)=A_45)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.62/1.40  tff(c_44, plain, (![A_46]: (m1_subset_1(k2_subset_1(A_46), k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.62/1.40  tff(c_55, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 2.62/1.40  tff(c_32, plain, (![A_41, B_42]: (r1_tarski(k1_zfmisc_1(A_41), k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.62/1.40  tff(c_159, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.62/1.40  tff(c_293, plain, (![B_113, B_114, A_115]: (r2_hidden(B_113, B_114) | ~r1_tarski(A_115, B_114) | ~m1_subset_1(B_113, A_115) | v1_xboole_0(A_115))), inference(resolution, [status(thm)], [c_36, c_159])).
% 2.62/1.40  tff(c_301, plain, (![B_113, B_42, A_41]: (r2_hidden(B_113, k1_zfmisc_1(B_42)) | ~m1_subset_1(B_113, k1_zfmisc_1(A_41)) | v1_xboole_0(k1_zfmisc_1(A_41)) | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_32, c_293])).
% 2.62/1.40  tff(c_340, plain, (![B_122, B_123, A_124]: (r2_hidden(B_122, k1_zfmisc_1(B_123)) | ~m1_subset_1(B_122, k1_zfmisc_1(A_124)) | ~r1_tarski(A_124, B_123))), inference(negUnitSimplification, [status(thm)], [c_46, c_301])).
% 2.62/1.40  tff(c_369, plain, (![A_130, B_131]: (r2_hidden(A_130, k1_zfmisc_1(B_131)) | ~r1_tarski(A_130, B_131))), inference(resolution, [status(thm)], [c_55, c_340])).
% 2.62/1.40  tff(c_34, plain, (![B_44, A_43]: (m1_subset_1(B_44, A_43) | ~r2_hidden(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.62/1.40  tff(c_378, plain, (![A_130, B_131]: (m1_subset_1(A_130, k1_zfmisc_1(B_131)) | v1_xboole_0(k1_zfmisc_1(B_131)) | ~r1_tarski(A_130, B_131))), inference(resolution, [status(thm)], [c_369, c_34])).
% 2.62/1.40  tff(c_388, plain, (![A_132, B_133]: (m1_subset_1(A_132, k1_zfmisc_1(B_133)) | ~r1_tarski(A_132, B_133))), inference(negUnitSimplification, [status(thm)], [c_46, c_378])).
% 2.62/1.40  tff(c_48, plain, (~m1_subset_1(k2_tarski('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.62/1.40  tff(c_406, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_388, c_48])).
% 2.62/1.40  tff(c_413, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_406])).
% 2.62/1.40  tff(c_415, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_413])).
% 2.62/1.40  tff(c_418, plain, (~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_415])).
% 2.62/1.40  tff(c_421, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_418])).
% 2.62/1.40  tff(c_423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_421])).
% 2.62/1.40  tff(c_424, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_413])).
% 2.62/1.40  tff(c_428, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_424])).
% 2.62/1.40  tff(c_431, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_428])).
% 2.62/1.40  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_431])).
% 2.62/1.40  tff(c_435, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_103])).
% 2.62/1.40  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.62/1.40  tff(c_442, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_435, c_12])).
% 2.62/1.40  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_442])).
% 2.62/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.40  
% 2.62/1.40  Inference rules
% 2.62/1.40  ----------------------
% 2.62/1.40  #Ref     : 0
% 2.62/1.40  #Sup     : 81
% 2.62/1.40  #Fact    : 0
% 2.62/1.40  #Define  : 0
% 2.62/1.40  #Split   : 2
% 2.62/1.40  #Chain   : 0
% 2.62/1.40  #Close   : 0
% 2.62/1.40  
% 2.62/1.40  Ordering : KBO
% 2.62/1.40  
% 2.62/1.40  Simplification rules
% 2.62/1.40  ----------------------
% 2.62/1.40  #Subsume      : 22
% 2.62/1.40  #Demod        : 4
% 2.62/1.40  #Tautology    : 23
% 2.62/1.40  #SimpNegUnit  : 13
% 2.62/1.40  #BackRed      : 0
% 2.62/1.40  
% 2.62/1.40  #Partial instantiations: 0
% 2.62/1.40  #Strategies tried      : 1
% 2.62/1.40  
% 2.62/1.40  Timing (in seconds)
% 2.62/1.40  ----------------------
% 2.62/1.40  Preprocessing        : 0.35
% 2.62/1.40  Parsing              : 0.19
% 2.62/1.40  CNF conversion       : 0.03
% 2.62/1.40  Main loop            : 0.25
% 2.62/1.40  Inferencing          : 0.10
% 2.62/1.40  Reduction            : 0.07
% 2.62/1.40  Demodulation         : 0.05
% 2.62/1.40  BG Simplification    : 0.02
% 2.62/1.40  Subsumption          : 0.04
% 2.62/1.40  Abstraction          : 0.01
% 2.62/1.40  MUC search           : 0.00
% 2.62/1.40  Cooper               : 0.00
% 2.62/1.40  Total                : 0.63
% 2.62/1.41  Index Insertion      : 0.00
% 2.62/1.41  Index Deletion       : 0.00
% 2.62/1.41  Index Matching       : 0.00
% 2.62/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
