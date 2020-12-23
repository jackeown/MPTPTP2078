%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:46 EST 2020

% Result     : Theorem 8.36s
% Output     : CNFRefutation 8.36s
% Verified   : 
% Statistics : Number of formulae       :   58 (  95 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 180 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14144,plain,(
    ! [A_701,B_702,C_703] :
      ( r2_hidden('#skF_5'(A_701,B_702,C_703),B_702)
      | r2_hidden('#skF_6'(A_701,B_702,C_703),C_703)
      | k2_zfmisc_1(A_701,B_702) = C_703 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_116,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_2'(A_69,B_70),B_70)
      | r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [B_73,A_74] :
      ( ~ v1_xboole_0(B_73)
      | r1_xboole_0(A_74,B_73) ) ),
    inference(resolution,[status(thm)],[c_116,c_2])).

tff(c_73,plain,(
    ! [A_60] :
      ( v1_xboole_0(A_60)
      | r2_hidden('#skF_1'(A_60),A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [B_54] :
      ( ~ r1_xboole_0(B_54,'#skF_10')
      | ~ r2_hidden(B_54,'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_81,plain,
    ( ~ r1_xboole_0('#skF_1'('#skF_10'),'#skF_10')
    | v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_73,c_46])).

tff(c_83,plain,(
    ~ r1_xboole_0('#skF_1'('#skF_10'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_144,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_136,c_83])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_172,plain,(
    ! [D_82,A_83,B_84] :
      ( ~ r2_hidden(D_82,'#skF_9'(A_83,B_84))
      | ~ r2_hidden(D_82,B_84)
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_13336,plain,(
    ! [A_603,B_604,B_605] :
      ( ~ r2_hidden('#skF_2'('#skF_9'(A_603,B_604),B_605),B_604)
      | ~ r2_hidden(A_603,B_604)
      | r1_xboole_0('#skF_9'(A_603,B_604),B_605) ) ),
    inference(resolution,[status(thm)],[c_10,c_172])).

tff(c_13342,plain,(
    ! [A_606,B_607] :
      ( ~ r2_hidden(A_606,B_607)
      | r1_xboole_0('#skF_9'(A_606,B_607),B_607) ) ),
    inference(resolution,[status(thm)],[c_8,c_13336])).

tff(c_126,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_9'(A_71,B_72),B_72)
      | ~ r2_hidden(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_134,plain,(
    ! [A_71] :
      ( ~ r1_xboole_0('#skF_9'(A_71,'#skF_10'),'#skF_10')
      | ~ r2_hidden(A_71,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_126,c_46])).

tff(c_13351,plain,(
    ! [A_608] : ~ r2_hidden(A_608,'#skF_10') ),
    inference(resolution,[status(thm)],[c_13342,c_134])).

tff(c_13423,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4,c_13351])).

tff(c_13443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_13423])).

tff(c_13444,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_13446,plain,(
    ! [A_609,B_610] :
      ( r2_hidden('#skF_2'(A_609,B_610),B_610)
      | r1_xboole_0(A_609,B_610) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_13455,plain,(
    ! [B_610,A_609] :
      ( ~ v1_xboole_0(B_610)
      | r1_xboole_0(A_609,B_610) ) ),
    inference(resolution,[status(thm)],[c_13446,c_2])).

tff(c_13468,plain,(
    ! [A_617,B_618] :
      ( r2_hidden('#skF_9'(A_617,B_618),B_618)
      | ~ r2_hidden(A_617,B_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_13489,plain,(
    ! [A_621] :
      ( ~ r1_xboole_0('#skF_9'(A_621,'#skF_10'),'#skF_10')
      | ~ r2_hidden(A_621,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_13468,c_46])).

tff(c_13495,plain,(
    ! [A_621] :
      ( ~ r2_hidden(A_621,'#skF_10')
      | ~ v1_xboole_0('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_13455,c_13489])).

tff(c_13499,plain,(
    ! [A_621] : ~ r2_hidden(A_621,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13444,c_13495])).

tff(c_14319,plain,(
    ! [A_711,B_712] :
      ( r2_hidden('#skF_5'(A_711,B_712,'#skF_10'),B_712)
      | k2_zfmisc_1(A_711,B_712) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_14144,c_13499])).

tff(c_14384,plain,(
    ! [A_713] : k2_zfmisc_1(A_713,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_14319,c_13499])).

tff(c_40,plain,(
    ! [B_45] : k2_zfmisc_1(k1_xboole_0,B_45) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14457,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_14384,c_40])).

tff(c_14490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_14457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:37:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.36/2.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.36/2.71  
% 8.36/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.36/2.71  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_9
% 8.36/2.71  
% 8.36/2.71  %Foreground sorts:
% 8.36/2.71  
% 8.36/2.71  
% 8.36/2.71  %Background operators:
% 8.36/2.71  
% 8.36/2.71  
% 8.36/2.71  %Foreground operators:
% 8.36/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.36/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.36/2.71  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.36/2.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.36/2.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.36/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.36/2.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.36/2.71  tff('#skF_10', type, '#skF_10': $i).
% 8.36/2.71  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 8.36/2.71  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.36/2.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.36/2.71  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 8.36/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.36/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.36/2.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.36/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.36/2.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.36/2.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.36/2.71  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 8.36/2.71  
% 8.36/2.72  tff(f_91, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 8.36/2.72  tff(f_61, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 8.36/2.72  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.36/2.72  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.36/2.72  tff(f_80, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 8.36/2.72  tff(f_67, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.36/2.72  tff(c_48, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.36/2.72  tff(c_14144, plain, (![A_701, B_702, C_703]: (r2_hidden('#skF_5'(A_701, B_702, C_703), B_702) | r2_hidden('#skF_6'(A_701, B_702, C_703), C_703) | k2_zfmisc_1(A_701, B_702)=C_703)), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.36/2.72  tff(c_116, plain, (![A_69, B_70]: (r2_hidden('#skF_2'(A_69, B_70), B_70) | r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.36/2.72  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.36/2.72  tff(c_136, plain, (![B_73, A_74]: (~v1_xboole_0(B_73) | r1_xboole_0(A_74, B_73))), inference(resolution, [status(thm)], [c_116, c_2])).
% 8.36/2.72  tff(c_73, plain, (![A_60]: (v1_xboole_0(A_60) | r2_hidden('#skF_1'(A_60), A_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.36/2.72  tff(c_46, plain, (![B_54]: (~r1_xboole_0(B_54, '#skF_10') | ~r2_hidden(B_54, '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.36/2.72  tff(c_81, plain, (~r1_xboole_0('#skF_1'('#skF_10'), '#skF_10') | v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_73, c_46])).
% 8.36/2.72  tff(c_83, plain, (~r1_xboole_0('#skF_1'('#skF_10'), '#skF_10')), inference(splitLeft, [status(thm)], [c_81])).
% 8.36/2.72  tff(c_144, plain, (~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_136, c_83])).
% 8.36/2.72  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.36/2.72  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.36/2.72  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.36/2.72  tff(c_172, plain, (![D_82, A_83, B_84]: (~r2_hidden(D_82, '#skF_9'(A_83, B_84)) | ~r2_hidden(D_82, B_84) | ~r2_hidden(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.36/2.72  tff(c_13336, plain, (![A_603, B_604, B_605]: (~r2_hidden('#skF_2'('#skF_9'(A_603, B_604), B_605), B_604) | ~r2_hidden(A_603, B_604) | r1_xboole_0('#skF_9'(A_603, B_604), B_605))), inference(resolution, [status(thm)], [c_10, c_172])).
% 8.36/2.72  tff(c_13342, plain, (![A_606, B_607]: (~r2_hidden(A_606, B_607) | r1_xboole_0('#skF_9'(A_606, B_607), B_607))), inference(resolution, [status(thm)], [c_8, c_13336])).
% 8.36/2.72  tff(c_126, plain, (![A_71, B_72]: (r2_hidden('#skF_9'(A_71, B_72), B_72) | ~r2_hidden(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.36/2.72  tff(c_134, plain, (![A_71]: (~r1_xboole_0('#skF_9'(A_71, '#skF_10'), '#skF_10') | ~r2_hidden(A_71, '#skF_10'))), inference(resolution, [status(thm)], [c_126, c_46])).
% 8.36/2.72  tff(c_13351, plain, (![A_608]: (~r2_hidden(A_608, '#skF_10'))), inference(resolution, [status(thm)], [c_13342, c_134])).
% 8.36/2.72  tff(c_13423, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4, c_13351])).
% 8.36/2.72  tff(c_13443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_13423])).
% 8.36/2.72  tff(c_13444, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_81])).
% 8.36/2.72  tff(c_13446, plain, (![A_609, B_610]: (r2_hidden('#skF_2'(A_609, B_610), B_610) | r1_xboole_0(A_609, B_610))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.36/2.72  tff(c_13455, plain, (![B_610, A_609]: (~v1_xboole_0(B_610) | r1_xboole_0(A_609, B_610))), inference(resolution, [status(thm)], [c_13446, c_2])).
% 8.36/2.72  tff(c_13468, plain, (![A_617, B_618]: (r2_hidden('#skF_9'(A_617, B_618), B_618) | ~r2_hidden(A_617, B_618))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.36/2.72  tff(c_13489, plain, (![A_621]: (~r1_xboole_0('#skF_9'(A_621, '#skF_10'), '#skF_10') | ~r2_hidden(A_621, '#skF_10'))), inference(resolution, [status(thm)], [c_13468, c_46])).
% 8.36/2.72  tff(c_13495, plain, (![A_621]: (~r2_hidden(A_621, '#skF_10') | ~v1_xboole_0('#skF_10'))), inference(resolution, [status(thm)], [c_13455, c_13489])).
% 8.36/2.72  tff(c_13499, plain, (![A_621]: (~r2_hidden(A_621, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_13444, c_13495])).
% 8.36/2.72  tff(c_14319, plain, (![A_711, B_712]: (r2_hidden('#skF_5'(A_711, B_712, '#skF_10'), B_712) | k2_zfmisc_1(A_711, B_712)='#skF_10')), inference(resolution, [status(thm)], [c_14144, c_13499])).
% 8.36/2.72  tff(c_14384, plain, (![A_713]: (k2_zfmisc_1(A_713, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_14319, c_13499])).
% 8.36/2.72  tff(c_40, plain, (![B_45]: (k2_zfmisc_1(k1_xboole_0, B_45)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.36/2.72  tff(c_14457, plain, (k1_xboole_0='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_14384, c_40])).
% 8.36/2.72  tff(c_14490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_14457])).
% 8.36/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.36/2.72  
% 8.36/2.72  Inference rules
% 8.36/2.72  ----------------------
% 8.36/2.72  #Ref     : 0
% 8.36/2.72  #Sup     : 3589
% 8.36/2.72  #Fact    : 0
% 8.36/2.72  #Define  : 0
% 8.36/2.72  #Split   : 3
% 8.36/2.72  #Chain   : 0
% 8.36/2.72  #Close   : 0
% 8.36/2.72  
% 8.36/2.72  Ordering : KBO
% 8.36/2.72  
% 8.36/2.72  Simplification rules
% 8.36/2.72  ----------------------
% 8.36/2.72  #Subsume      : 819
% 8.36/2.72  #Demod        : 3525
% 8.36/2.72  #Tautology    : 1905
% 8.36/2.72  #SimpNegUnit  : 28
% 8.36/2.72  #BackRed      : 6
% 8.36/2.72  
% 8.36/2.72  #Partial instantiations: 0
% 8.36/2.72  #Strategies tried      : 1
% 8.36/2.72  
% 8.36/2.72  Timing (in seconds)
% 8.36/2.72  ----------------------
% 8.36/2.72  Preprocessing        : 0.31
% 8.36/2.72  Parsing              : 0.15
% 8.36/2.73  CNF conversion       : 0.03
% 8.36/2.73  Main loop            : 1.66
% 8.36/2.73  Inferencing          : 0.54
% 8.36/2.73  Reduction            : 0.43
% 8.36/2.73  Demodulation         : 0.30
% 8.36/2.73  BG Simplification    : 0.06
% 8.36/2.73  Subsumption          : 0.53
% 8.36/2.73  Abstraction          : 0.08
% 8.36/2.73  MUC search           : 0.00
% 8.36/2.73  Cooper               : 0.00
% 8.36/2.73  Total                : 2.00
% 8.50/2.73  Index Insertion      : 0.00
% 8.50/2.73  Index Deletion       : 0.00
% 8.50/2.73  Index Matching       : 0.00
% 8.50/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
