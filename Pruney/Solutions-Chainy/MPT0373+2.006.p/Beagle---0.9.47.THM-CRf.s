%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:57 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 116 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 229 expanded)
%              Number of equality atoms :    8 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_86,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_90,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_91,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_350,plain,(
    ! [A_87,B_88,C_89] :
      ( r1_tarski(k2_tarski(A_87,B_88),C_89)
      | ~ r2_hidden(B_88,C_89)
      | ~ r2_hidden(A_87,C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( r2_hidden(B_21,A_20)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(k2_tarski(A_56,B_57),C_58)
      | ~ r2_hidden(B_57,C_58)
      | ~ r2_hidden(A_56,C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_201,plain,(
    ! [A_65,C_66] :
      ( r1_tarski(k1_tarski(A_65),C_66)
      | ~ r2_hidden(A_65,C_66)
      | ~ r2_hidden(A_65,C_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_149])).

tff(c_92,plain,(
    ! [B_37,A_38] :
      ( m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(B_37)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_100,plain,
    ( ~ v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_92,c_40])).

tff(c_105,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_16,plain,(
    ! [C_16,A_12] :
      ( r2_hidden(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_111,plain,(
    ! [B_47,A_48] :
      ( m1_subset_1(B_47,A_48)
      | ~ r2_hidden(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_161,plain,(
    ! [C_59,A_60] :
      ( m1_subset_1(C_59,k1_zfmisc_1(A_60))
      | v1_xboole_0(k1_zfmisc_1(A_60))
      | ~ r1_tarski(C_59,A_60) ) ),
    inference(resolution,[status(thm)],[c_16,c_111])).

tff(c_167,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_161,c_40])).

tff(c_171,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_167])).

tff(c_208,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_201,c_171])).

tff(c_212,plain,
    ( ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_208])).

tff(c_215,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_212])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_215])).

tff(c_219,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_61,plain,(
    ! [C_27,A_28] :
      ( r2_hidden(C_27,k1_zfmisc_1(A_28))
      | ~ r1_tarski(C_27,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_28,C_27] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_28))
      | ~ r1_tarski(C_27,A_28) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_225,plain,(
    ! [C_27] : ~ r1_tarski(C_27,'#skF_4') ),
    inference(resolution,[status(thm)],[c_219,c_65])).

tff(c_365,plain,(
    ! [B_88,A_87] :
      ( ~ r2_hidden(B_88,'#skF_4')
      | ~ r2_hidden(A_87,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_350,c_225])).

tff(c_368,plain,(
    ! [A_90] : ~ r2_hidden(A_90,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_376,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_368])).

tff(c_383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_376])).

tff(c_385,plain,(
    ! [B_91] : ~ r2_hidden(B_91,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_393,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_385])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_393])).

tff(c_402,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_409,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_402,c_6])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:36:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.14/1.30  
% 2.14/1.30  %Foreground sorts:
% 2.14/1.30  
% 2.14/1.30  
% 2.14/1.30  %Background operators:
% 2.14/1.30  
% 2.14/1.30  
% 2.14/1.30  %Foreground operators:
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.14/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.14/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.30  
% 2.14/1.31  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.14/1.31  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.14/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.14/1.31  tff(f_54, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.14/1.31  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.14/1.31  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.14/1.31  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.14/1.31  tff(c_42, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.31  tff(c_44, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.31  tff(c_86, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.14/1.31  tff(c_90, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_86])).
% 2.14/1.31  tff(c_91, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_90])).
% 2.14/1.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.31  tff(c_350, plain, (![A_87, B_88, C_89]: (r1_tarski(k2_tarski(A_87, B_88), C_89) | ~r2_hidden(B_88, C_89) | ~r2_hidden(A_87, C_89))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.31  tff(c_34, plain, (![B_21, A_20]: (r2_hidden(B_21, A_20) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.14/1.31  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.31  tff(c_149, plain, (![A_56, B_57, C_58]: (r1_tarski(k2_tarski(A_56, B_57), C_58) | ~r2_hidden(B_57, C_58) | ~r2_hidden(A_56, C_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.31  tff(c_201, plain, (![A_65, C_66]: (r1_tarski(k1_tarski(A_65), C_66) | ~r2_hidden(A_65, C_66) | ~r2_hidden(A_65, C_66))), inference(superposition, [status(thm), theory('equality')], [c_8, c_149])).
% 2.14/1.31  tff(c_92, plain, (![B_37, A_38]: (m1_subset_1(B_37, A_38) | ~v1_xboole_0(B_37) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.14/1.31  tff(c_40, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.31  tff(c_100, plain, (~v1_xboole_0(k1_tarski('#skF_5')) | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_92, c_40])).
% 2.14/1.31  tff(c_105, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_100])).
% 2.14/1.31  tff(c_16, plain, (![C_16, A_12]: (r2_hidden(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.31  tff(c_111, plain, (![B_47, A_48]: (m1_subset_1(B_47, A_48) | ~r2_hidden(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.14/1.31  tff(c_161, plain, (![C_59, A_60]: (m1_subset_1(C_59, k1_zfmisc_1(A_60)) | v1_xboole_0(k1_zfmisc_1(A_60)) | ~r1_tarski(C_59, A_60))), inference(resolution, [status(thm)], [c_16, c_111])).
% 2.14/1.31  tff(c_167, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_161, c_40])).
% 2.14/1.31  tff(c_171, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_105, c_167])).
% 2.14/1.31  tff(c_208, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_201, c_171])).
% 2.14/1.31  tff(c_212, plain, (~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_208])).
% 2.14/1.31  tff(c_215, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_212])).
% 2.14/1.31  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_215])).
% 2.14/1.31  tff(c_219, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_100])).
% 2.14/1.31  tff(c_61, plain, (![C_27, A_28]: (r2_hidden(C_27, k1_zfmisc_1(A_28)) | ~r1_tarski(C_27, A_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.31  tff(c_65, plain, (![A_28, C_27]: (~v1_xboole_0(k1_zfmisc_1(A_28)) | ~r1_tarski(C_27, A_28))), inference(resolution, [status(thm)], [c_61, c_2])).
% 2.14/1.31  tff(c_225, plain, (![C_27]: (~r1_tarski(C_27, '#skF_4'))), inference(resolution, [status(thm)], [c_219, c_65])).
% 2.14/1.31  tff(c_365, plain, (![B_88, A_87]: (~r2_hidden(B_88, '#skF_4') | ~r2_hidden(A_87, '#skF_4'))), inference(resolution, [status(thm)], [c_350, c_225])).
% 2.14/1.31  tff(c_368, plain, (![A_90]: (~r2_hidden(A_90, '#skF_4'))), inference(splitLeft, [status(thm)], [c_365])).
% 2.14/1.31  tff(c_376, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_368])).
% 2.14/1.31  tff(c_383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_376])).
% 2.14/1.31  tff(c_385, plain, (![B_91]: (~r2_hidden(B_91, '#skF_4'))), inference(splitRight, [status(thm)], [c_365])).
% 2.14/1.31  tff(c_393, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_385])).
% 2.14/1.31  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_393])).
% 2.14/1.31  tff(c_402, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_90])).
% 2.14/1.31  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.31  tff(c_409, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_402, c_6])).
% 2.14/1.31  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_409])).
% 2.14/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.31  
% 2.14/1.31  Inference rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Ref     : 0
% 2.14/1.31  #Sup     : 73
% 2.14/1.31  #Fact    : 0
% 2.14/1.31  #Define  : 0
% 2.14/1.31  #Split   : 3
% 2.14/1.31  #Chain   : 0
% 2.14/1.31  #Close   : 0
% 2.14/1.31  
% 2.14/1.31  Ordering : KBO
% 2.14/1.31  
% 2.14/1.31  Simplification rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Subsume      : 11
% 2.14/1.31  #Demod        : 14
% 2.14/1.31  #Tautology    : 34
% 2.14/1.31  #SimpNegUnit  : 10
% 2.14/1.31  #BackRed      : 2
% 2.14/1.31  
% 2.14/1.31  #Partial instantiations: 0
% 2.14/1.31  #Strategies tried      : 1
% 2.14/1.31  
% 2.14/1.31  Timing (in seconds)
% 2.14/1.31  ----------------------
% 2.14/1.31  Preprocessing        : 0.29
% 2.14/1.31  Parsing              : 0.15
% 2.14/1.31  CNF conversion       : 0.02
% 2.14/1.31  Main loop            : 0.22
% 2.14/1.31  Inferencing          : 0.09
% 2.14/1.31  Reduction            : 0.06
% 2.14/1.31  Demodulation         : 0.03
% 2.14/1.31  BG Simplification    : 0.02
% 2.14/1.31  Subsumption          : 0.04
% 2.14/1.32  Abstraction          : 0.01
% 2.14/1.32  MUC search           : 0.00
% 2.14/1.32  Cooper               : 0.00
% 2.14/1.32  Total                : 0.54
% 2.14/1.32  Index Insertion      : 0.00
% 2.14/1.32  Index Deletion       : 0.00
% 2.14/1.32  Index Matching       : 0.00
% 2.14/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
