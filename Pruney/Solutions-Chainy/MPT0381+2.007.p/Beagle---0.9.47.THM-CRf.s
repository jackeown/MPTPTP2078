%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:02 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   65 (  94 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 130 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_85,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_54,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ! [B_38,A_39] :
      ( ~ r2_hidden(B_38,A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_66])).

tff(c_134,plain,(
    ! [B_58,A_59] :
      ( m1_subset_1(B_58,A_59)
      | ~ r2_hidden(B_58,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_146,plain,
    ( m1_subset_1('#skF_5','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_134])).

tff(c_154,plain,(
    m1_subset_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_146])).

tff(c_325,plain,(
    ! [B_80,A_81] :
      ( m1_subset_1(k1_tarski(B_80),k1_zfmisc_1(A_81))
      | k1_xboole_0 = A_81
      | ~ m1_subset_1(B_80,A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_334,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_325,c_52])).

tff(c_339,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_334])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [A_32] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_182,plain,(
    ! [B_65,A_66] :
      ( r2_hidden(B_65,A_66)
      | ~ m1_subset_1(B_65,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [C_25,A_21] :
      ( r1_tarski(C_25,A_21)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_189,plain,(
    ! [B_65,A_21] :
      ( r1_tarski(B_65,A_21)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_182,c_20])).

tff(c_219,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(B_70,A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_189])).

tff(c_240,plain,(
    ! [A_72] : r1_tarski(k1_xboole_0,A_72) ),
    inference(resolution,[status(thm)],[c_48,c_219])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_245,plain,(
    ! [A_73] : k3_xboole_0(k1_xboole_0,A_73) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_240,c_10])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_264,plain,(
    ! [A_77] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_8])).

tff(c_34,plain,(
    ! [C_28,B_27] : ~ r2_hidden(C_28,k4_xboole_0(B_27,k1_tarski(C_28))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_280,plain,(
    ! [C_78] : ~ r2_hidden(C_78,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_34])).

tff(c_295,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_280])).

tff(c_274,plain,(
    ! [C_28] : ~ r2_hidden(C_28,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_34])).

tff(c_303,plain,(
    ! [C_79] : ~ r2_hidden(C_79,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_274])).

tff(c_319,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_303])).

tff(c_341,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_319])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.28  
% 2.43/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.28  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 2.43/1.28  
% 2.43/1.28  %Foreground sorts:
% 2.43/1.28  
% 2.43/1.28  
% 2.43/1.28  %Background operators:
% 2.43/1.28  
% 2.43/1.28  
% 2.43/1.28  %Foreground operators:
% 2.43/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.43/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.43/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.43/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.43/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.43/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.43/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.43/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.43/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.43/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.43/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.28  
% 2.43/1.30  tff(f_97, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.43/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.43/1.30  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.43/1.30  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.43/1.30  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.43/1.30  tff(f_85, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.43/1.30  tff(f_83, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.43/1.30  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.43/1.30  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.43/1.30  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.43/1.30  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.43/1.30  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.43/1.30  tff(c_66, plain, (![B_38, A_39]: (~r2_hidden(B_38, A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.30  tff(c_70, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_66])).
% 2.43/1.30  tff(c_134, plain, (![B_58, A_59]: (m1_subset_1(B_58, A_59) | ~r2_hidden(B_58, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.30  tff(c_146, plain, (m1_subset_1('#skF_5', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_134])).
% 2.43/1.30  tff(c_154, plain, (m1_subset_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_146])).
% 2.43/1.30  tff(c_325, plain, (![B_80, A_81]: (m1_subset_1(k1_tarski(B_80), k1_zfmisc_1(A_81)) | k1_xboole_0=A_81 | ~m1_subset_1(B_80, A_81))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.43/1.30  tff(c_52, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.43/1.30  tff(c_334, plain, (k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_325, c_52])).
% 2.43/1.30  tff(c_339, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_334])).
% 2.43/1.30  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.30  tff(c_6, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.43/1.30  tff(c_48, plain, (![A_32]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.43/1.30  tff(c_46, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.43/1.30  tff(c_182, plain, (![B_65, A_66]: (r2_hidden(B_65, A_66) | ~m1_subset_1(B_65, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.30  tff(c_20, plain, (![C_25, A_21]: (r1_tarski(C_25, A_21) | ~r2_hidden(C_25, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.43/1.30  tff(c_189, plain, (![B_65, A_21]: (r1_tarski(B_65, A_21) | ~m1_subset_1(B_65, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_182, c_20])).
% 2.43/1.30  tff(c_219, plain, (![B_70, A_71]: (r1_tarski(B_70, A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)))), inference(negUnitSimplification, [status(thm)], [c_46, c_189])).
% 2.43/1.30  tff(c_240, plain, (![A_72]: (r1_tarski(k1_xboole_0, A_72))), inference(resolution, [status(thm)], [c_48, c_219])).
% 2.43/1.30  tff(c_10, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.30  tff(c_245, plain, (![A_73]: (k3_xboole_0(k1_xboole_0, A_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_240, c_10])).
% 2.43/1.30  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.43/1.30  tff(c_264, plain, (![A_77]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_77))), inference(superposition, [status(thm), theory('equality')], [c_245, c_8])).
% 2.43/1.30  tff(c_34, plain, (![C_28, B_27]: (~r2_hidden(C_28, k4_xboole_0(B_27, k1_tarski(C_28))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.43/1.30  tff(c_280, plain, (![C_78]: (~r2_hidden(C_78, k5_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_34])).
% 2.43/1.30  tff(c_295, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_280])).
% 2.43/1.30  tff(c_274, plain, (![C_28]: (~r2_hidden(C_28, k5_xboole_0(k1_xboole_0, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_34])).
% 2.43/1.30  tff(c_303, plain, (![C_79]: (~r2_hidden(C_79, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_274])).
% 2.43/1.30  tff(c_319, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_303])).
% 2.43/1.30  tff(c_341, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_319])).
% 2.43/1.30  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_341])).
% 2.43/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.30  
% 2.43/1.30  Inference rules
% 2.43/1.30  ----------------------
% 2.43/1.30  #Ref     : 0
% 2.43/1.30  #Sup     : 61
% 2.43/1.30  #Fact    : 0
% 2.43/1.30  #Define  : 0
% 2.43/1.30  #Split   : 0
% 2.43/1.30  #Chain   : 0
% 2.43/1.30  #Close   : 0
% 2.43/1.30  
% 2.43/1.30  Ordering : KBO
% 2.43/1.30  
% 2.43/1.30  Simplification rules
% 2.43/1.30  ----------------------
% 2.43/1.30  #Subsume      : 7
% 2.43/1.30  #Demod        : 16
% 2.43/1.30  #Tautology    : 24
% 2.43/1.30  #SimpNegUnit  : 6
% 2.43/1.30  #BackRed      : 11
% 2.43/1.30  
% 2.43/1.30  #Partial instantiations: 0
% 2.43/1.30  #Strategies tried      : 1
% 2.43/1.30  
% 2.43/1.30  Timing (in seconds)
% 2.43/1.30  ----------------------
% 2.43/1.30  Preprocessing        : 0.33
% 2.43/1.30  Parsing              : 0.17
% 2.43/1.30  CNF conversion       : 0.02
% 2.43/1.30  Main loop            : 0.21
% 2.43/1.30  Inferencing          : 0.08
% 2.43/1.30  Reduction            : 0.07
% 2.43/1.30  Demodulation         : 0.04
% 2.43/1.30  BG Simplification    : 0.02
% 2.43/1.30  Subsumption          : 0.03
% 2.43/1.30  Abstraction          : 0.02
% 2.43/1.30  MUC search           : 0.00
% 2.43/1.30  Cooper               : 0.00
% 2.43/1.30  Total                : 0.57
% 2.43/1.30  Index Insertion      : 0.00
% 2.43/1.30  Index Deletion       : 0.00
% 2.43/1.30  Index Matching       : 0.00
% 2.43/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
