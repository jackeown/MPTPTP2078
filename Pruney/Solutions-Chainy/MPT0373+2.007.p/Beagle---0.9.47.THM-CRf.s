%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:57 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 127 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 255 expanded)
%              Number of equality atoms :    9 (  25 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_65,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
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

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_216,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_224,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_216])).

tff(c_237,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_296,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(k2_tarski(A_76,B_77),C_78)
      | ~ r2_hidden(B_77,C_78)
      | ~ r2_hidden(A_76,C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_89,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_81])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( r2_hidden(B_18,A_17)
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(k2_tarski(A_52,B_53),C_54)
      | ~ r2_hidden(B_53,C_54)
      | ~ r2_hidden(A_52,C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_161,plain,(
    ! [A_55,C_56] :
      ( r1_tarski(k1_tarski(A_55),C_56)
      | ~ r2_hidden(A_55,C_56)
      | ~ r2_hidden(A_55,C_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_149])).

tff(c_74,plain,(
    ! [B_28,A_29] :
      ( m1_subset_1(B_28,A_29)
      | ~ v1_xboole_0(B_28)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_78,plain,
    ( ~ v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_38])).

tff(c_80,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_14,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_119,plain,(
    ! [B_46,A_47] :
      ( m1_subset_1(B_46,A_47)
      | ~ r2_hidden(B_46,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,(
    ! [C_50,A_51] :
      ( m1_subset_1(C_50,k1_zfmisc_1(A_51))
      | v1_xboole_0(k1_zfmisc_1(A_51))
      | ~ r1_tarski(C_50,A_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_119])).

tff(c_144,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_138,c_38])).

tff(c_148,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_144])).

tff(c_168,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_161,c_148])).

tff(c_172,plain,
    ( ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_168])).

tff(c_175,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_172])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_175])).

tff(c_179,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_186,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_179,c_6])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_186])).

tff(c_192,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_65,plain,(
    ! [C_26,A_27] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_27))
      | ~ r1_tarski(C_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_27,C_26] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_27))
      | ~ r1_tarski(C_26,A_27) ) ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_198,plain,(
    ! [C_26] : ~ r1_tarski(C_26,'#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_73])).

tff(c_312,plain,(
    ! [B_77,A_76] :
      ( ~ r2_hidden(B_77,'#skF_4')
      | ~ r2_hidden(A_76,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_296,c_198])).

tff(c_314,plain,(
    ! [A_79] : ~ r2_hidden(A_79,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_322,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_314])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_322])).

tff(c_331,plain,(
    ! [B_80] : ~ r2_hidden(B_80,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_339,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_331])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_339])).

tff(c_348,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_355,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_348,c_6])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.22/1.32  
% 2.22/1.32  %Foreground sorts:
% 2.22/1.32  
% 2.22/1.32  
% 2.22/1.32  %Background operators:
% 2.22/1.32  
% 2.22/1.32  
% 2.22/1.32  %Foreground operators:
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.22/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.22/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.32  
% 2.22/1.33  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.22/1.33  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.22/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.22/1.33  tff(f_52, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.22/1.33  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.22/1.33  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.22/1.33  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.22/1.33  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.33  tff(c_42, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.33  tff(c_216, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, A_59) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.33  tff(c_224, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_216])).
% 2.22/1.33  tff(c_237, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_224])).
% 2.22/1.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.33  tff(c_296, plain, (![A_76, B_77, C_78]: (r1_tarski(k2_tarski(A_76, B_77), C_78) | ~r2_hidden(B_77, C_78) | ~r2_hidden(A_76, C_78))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.33  tff(c_81, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.33  tff(c_89, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_81])).
% 2.22/1.33  tff(c_90, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_89])).
% 2.22/1.33  tff(c_32, plain, (![B_18, A_17]: (r2_hidden(B_18, A_17) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.33  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.22/1.33  tff(c_149, plain, (![A_52, B_53, C_54]: (r1_tarski(k2_tarski(A_52, B_53), C_54) | ~r2_hidden(B_53, C_54) | ~r2_hidden(A_52, C_54))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.33  tff(c_161, plain, (![A_55, C_56]: (r1_tarski(k1_tarski(A_55), C_56) | ~r2_hidden(A_55, C_56) | ~r2_hidden(A_55, C_56))), inference(superposition, [status(thm), theory('equality')], [c_8, c_149])).
% 2.22/1.33  tff(c_74, plain, (![B_28, A_29]: (m1_subset_1(B_28, A_29) | ~v1_xboole_0(B_28) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.33  tff(c_38, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.33  tff(c_78, plain, (~v1_xboole_0(k1_tarski('#skF_5')) | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_74, c_38])).
% 2.22/1.33  tff(c_80, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_78])).
% 2.22/1.33  tff(c_14, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.22/1.33  tff(c_119, plain, (![B_46, A_47]: (m1_subset_1(B_46, A_47) | ~r2_hidden(B_46, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.33  tff(c_138, plain, (![C_50, A_51]: (m1_subset_1(C_50, k1_zfmisc_1(A_51)) | v1_xboole_0(k1_zfmisc_1(A_51)) | ~r1_tarski(C_50, A_51))), inference(resolution, [status(thm)], [c_14, c_119])).
% 2.22/1.33  tff(c_144, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_138, c_38])).
% 2.22/1.33  tff(c_148, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_144])).
% 2.22/1.33  tff(c_168, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_161, c_148])).
% 2.22/1.33  tff(c_172, plain, (~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_32, c_168])).
% 2.22/1.33  tff(c_175, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_172])).
% 2.22/1.33  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_175])).
% 2.22/1.33  tff(c_179, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_89])).
% 2.22/1.33  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.33  tff(c_186, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_179, c_6])).
% 2.22/1.33  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_186])).
% 2.22/1.33  tff(c_192, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_78])).
% 2.22/1.33  tff(c_65, plain, (![C_26, A_27]: (r2_hidden(C_26, k1_zfmisc_1(A_27)) | ~r1_tarski(C_26, A_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.22/1.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.33  tff(c_73, plain, (![A_27, C_26]: (~v1_xboole_0(k1_zfmisc_1(A_27)) | ~r1_tarski(C_26, A_27))), inference(resolution, [status(thm)], [c_65, c_2])).
% 2.22/1.33  tff(c_198, plain, (![C_26]: (~r1_tarski(C_26, '#skF_4'))), inference(resolution, [status(thm)], [c_192, c_73])).
% 2.22/1.33  tff(c_312, plain, (![B_77, A_76]: (~r2_hidden(B_77, '#skF_4') | ~r2_hidden(A_76, '#skF_4'))), inference(resolution, [status(thm)], [c_296, c_198])).
% 2.22/1.33  tff(c_314, plain, (![A_79]: (~r2_hidden(A_79, '#skF_4'))), inference(splitLeft, [status(thm)], [c_312])).
% 2.22/1.33  tff(c_322, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_314])).
% 2.22/1.33  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_322])).
% 2.22/1.33  tff(c_331, plain, (![B_80]: (~r2_hidden(B_80, '#skF_4'))), inference(splitRight, [status(thm)], [c_312])).
% 2.22/1.33  tff(c_339, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_331])).
% 2.22/1.33  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_339])).
% 2.22/1.33  tff(c_348, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_224])).
% 2.22/1.33  tff(c_355, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_348, c_6])).
% 2.22/1.33  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_355])).
% 2.22/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.33  
% 2.22/1.33  Inference rules
% 2.22/1.33  ----------------------
% 2.22/1.33  #Ref     : 0
% 2.22/1.33  #Sup     : 62
% 2.22/1.33  #Fact    : 0
% 2.22/1.33  #Define  : 0
% 2.22/1.33  #Split   : 4
% 2.22/1.33  #Chain   : 0
% 2.22/1.33  #Close   : 0
% 2.22/1.33  
% 2.22/1.33  Ordering : KBO
% 2.22/1.33  
% 2.22/1.33  Simplification rules
% 2.22/1.33  ----------------------
% 2.22/1.33  #Subsume      : 6
% 2.22/1.33  #Demod        : 6
% 2.22/1.33  #Tautology    : 26
% 2.22/1.33  #SimpNegUnit  : 9
% 2.22/1.33  #BackRed      : 2
% 2.22/1.33  
% 2.22/1.33  #Partial instantiations: 0
% 2.22/1.33  #Strategies tried      : 1
% 2.22/1.33  
% 2.22/1.33  Timing (in seconds)
% 2.22/1.33  ----------------------
% 2.22/1.33  Preprocessing        : 0.31
% 2.22/1.33  Parsing              : 0.17
% 2.22/1.33  CNF conversion       : 0.02
% 2.22/1.33  Main loop            : 0.20
% 2.22/1.33  Inferencing          : 0.08
% 2.22/1.33  Reduction            : 0.05
% 2.22/1.33  Demodulation         : 0.03
% 2.22/1.33  BG Simplification    : 0.02
% 2.22/1.34  Subsumption          : 0.03
% 2.22/1.34  Abstraction          : 0.01
% 2.22/1.34  MUC search           : 0.00
% 2.22/1.34  Cooper               : 0.00
% 2.22/1.34  Total                : 0.55
% 2.22/1.34  Index Insertion      : 0.00
% 2.22/1.34  Index Deletion       : 0.00
% 2.22/1.34  Index Matching       : 0.00
% 2.22/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
