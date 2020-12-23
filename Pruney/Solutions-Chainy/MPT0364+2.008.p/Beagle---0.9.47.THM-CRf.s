%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:40 EST 2020

% Result     : Theorem 6.83s
% Output     : CNFRefutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :   60 (  93 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 181 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_70,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_108,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_34])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_113,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k3_subset_1(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_121,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_113])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,k4_xboole_0(C_10,B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_309,plain,(
    ! [A_70] :
      ( r1_xboole_0(A_70,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_70,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_14])).

tff(c_312,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_309,c_70])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_312])).

tff(c_319,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_371,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(A_88,B_89) = k3_subset_1(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_379,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_371])).

tff(c_44,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(A_27,B_28)
      | ~ r1_tarski(A_27,k4_xboole_0(B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [B_28,C_29] : r1_tarski(k4_xboole_0(B_28,C_29),B_28) ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_441,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_49])).

tff(c_320,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_323,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_320,c_2])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(A_11,k4_xboole_0(B_12,C_13))
      | ~ r1_xboole_0(A_11,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_350,plain,(
    ! [B_80,A_81] :
      ( B_80 = A_81
      | ~ r1_tarski(B_80,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_647,plain,(
    ! [B_113,C_114] :
      ( k4_xboole_0(B_113,C_114) = B_113
      | ~ r1_tarski(B_113,k4_xboole_0(B_113,C_114)) ) ),
    inference(resolution,[status(thm)],[c_49,c_350])).

tff(c_651,plain,(
    ! [B_12,C_13] :
      ( k4_xboole_0(B_12,C_13) = B_12
      | ~ r1_xboole_0(B_12,C_13)
      | ~ r1_tarski(B_12,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_647])).

tff(c_663,plain,(
    ! [B_115,C_116] :
      ( k4_xboole_0(B_115,C_116) = B_115
      | ~ r1_xboole_0(B_115,C_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_651])).

tff(c_740,plain,(
    k4_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_323,c_663])).

tff(c_363,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_xboole_0(A_82,k4_xboole_0(C_83,B_84))
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_366,plain,(
    ! [C_83,B_84,A_82] :
      ( r1_xboole_0(k4_xboole_0(C_83,B_84),A_82)
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(resolution,[status(thm)],[c_363,c_2])).

tff(c_1455,plain,(
    ! [A_82] :
      ( r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),A_82)
      | ~ r1_tarski(A_82,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_366])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_378,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_371])).

tff(c_469,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(A_90,k4_xboole_0(B_91,C_92))
      | ~ r1_xboole_0(A_90,C_92)
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1384,plain,(
    ! [A_144] :
      ( r1_tarski(A_144,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_144,'#skF_2')
      | ~ r1_tarski(A_144,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_469])).

tff(c_20,plain,(
    ! [B_17,C_19,A_16] :
      ( r1_tarski(B_17,C_19)
      | ~ r1_tarski(k3_subset_1(A_16,C_19),k3_subset_1(A_16,B_17))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1402,plain,(
    ! [C_19] :
      ( r1_tarski('#skF_2',C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ r1_xboole_0(k3_subset_1('#skF_1',C_19),'#skF_2')
      | ~ r1_tarski(k3_subset_1('#skF_1',C_19),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1384,c_20])).

tff(c_9067,plain,(
    ! [C_303] :
      ( r1_tarski('#skF_2',C_303)
      | ~ m1_subset_1(C_303,k1_zfmisc_1('#skF_1'))
      | ~ r1_xboole_0(k3_subset_1('#skF_1',C_303),'#skF_2')
      | ~ r1_tarski(k3_subset_1('#skF_1',C_303),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1402])).

tff(c_9077,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1455,c_9067])).

tff(c_9096,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_441,c_24,c_9077])).

tff(c_9098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_9096])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:54:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.83/2.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.54  
% 6.83/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.55  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.83/2.55  
% 6.83/2.55  %Foreground sorts:
% 6.83/2.55  
% 6.83/2.55  
% 6.83/2.55  %Background operators:
% 6.83/2.55  
% 6.83/2.55  
% 6.83/2.55  %Foreground operators:
% 6.83/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.83/2.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.83/2.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.83/2.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.83/2.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.83/2.55  tff('#skF_2', type, '#skF_2': $i).
% 6.83/2.55  tff('#skF_3', type, '#skF_3': $i).
% 6.83/2.55  tff('#skF_1', type, '#skF_1': $i).
% 6.83/2.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.83/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.83/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.83/2.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.83/2.55  
% 6.83/2.56  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 6.83/2.56  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.83/2.56  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 6.83/2.56  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.83/2.56  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.83/2.56  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.83/2.56  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 6.83/2.56  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 6.83/2.56  tff(c_28, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.83/2.56  tff(c_70, plain, (~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_28])).
% 6.83/2.56  tff(c_34, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.83/2.56  tff(c_108, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_34])).
% 6.83/2.56  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.83/2.56  tff(c_113, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k3_subset_1(A_50, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.83/2.56  tff(c_121, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_113])).
% 6.83/2.56  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, k4_xboole_0(C_10, B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.83/2.56  tff(c_309, plain, (![A_70]: (r1_xboole_0(A_70, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_70, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_14])).
% 6.83/2.56  tff(c_312, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_309, c_70])).
% 6.83/2.56  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_312])).
% 6.83/2.56  tff(c_319, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 6.83/2.56  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.83/2.56  tff(c_371, plain, (![A_88, B_89]: (k4_xboole_0(A_88, B_89)=k3_subset_1(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.83/2.56  tff(c_379, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_371])).
% 6.83/2.56  tff(c_44, plain, (![A_27, B_28, C_29]: (r1_tarski(A_27, B_28) | ~r1_tarski(A_27, k4_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.83/2.56  tff(c_49, plain, (![B_28, C_29]: (r1_tarski(k4_xboole_0(B_28, C_29), B_28))), inference(resolution, [status(thm)], [c_8, c_44])).
% 6.83/2.56  tff(c_441, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_379, c_49])).
% 6.83/2.56  tff(c_320, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 6.83/2.56  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.83/2.56  tff(c_323, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_320, c_2])).
% 6.83/2.56  tff(c_16, plain, (![A_11, B_12, C_13]: (r1_tarski(A_11, k4_xboole_0(B_12, C_13)) | ~r1_xboole_0(A_11, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.83/2.56  tff(c_350, plain, (![B_80, A_81]: (B_80=A_81 | ~r1_tarski(B_80, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.83/2.56  tff(c_647, plain, (![B_113, C_114]: (k4_xboole_0(B_113, C_114)=B_113 | ~r1_tarski(B_113, k4_xboole_0(B_113, C_114)))), inference(resolution, [status(thm)], [c_49, c_350])).
% 6.83/2.56  tff(c_651, plain, (![B_12, C_13]: (k4_xboole_0(B_12, C_13)=B_12 | ~r1_xboole_0(B_12, C_13) | ~r1_tarski(B_12, B_12))), inference(resolution, [status(thm)], [c_16, c_647])).
% 6.83/2.56  tff(c_663, plain, (![B_115, C_116]: (k4_xboole_0(B_115, C_116)=B_115 | ~r1_xboole_0(B_115, C_116))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_651])).
% 6.83/2.56  tff(c_740, plain, (k4_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_323, c_663])).
% 6.83/2.56  tff(c_363, plain, (![A_82, C_83, B_84]: (r1_xboole_0(A_82, k4_xboole_0(C_83, B_84)) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.83/2.56  tff(c_366, plain, (![C_83, B_84, A_82]: (r1_xboole_0(k4_xboole_0(C_83, B_84), A_82) | ~r1_tarski(A_82, B_84))), inference(resolution, [status(thm)], [c_363, c_2])).
% 6.83/2.56  tff(c_1455, plain, (![A_82]: (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), A_82) | ~r1_tarski(A_82, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_740, c_366])).
% 6.83/2.56  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.83/2.56  tff(c_378, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_371])).
% 6.83/2.56  tff(c_469, plain, (![A_90, B_91, C_92]: (r1_tarski(A_90, k4_xboole_0(B_91, C_92)) | ~r1_xboole_0(A_90, C_92) | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.83/2.56  tff(c_1384, plain, (![A_144]: (r1_tarski(A_144, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_144, '#skF_2') | ~r1_tarski(A_144, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_378, c_469])).
% 6.83/2.56  tff(c_20, plain, (![B_17, C_19, A_16]: (r1_tarski(B_17, C_19) | ~r1_tarski(k3_subset_1(A_16, C_19), k3_subset_1(A_16, B_17)) | ~m1_subset_1(C_19, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.83/2.56  tff(c_1402, plain, (![C_19]: (r1_tarski('#skF_2', C_19) | ~m1_subset_1(C_19, k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~r1_xboole_0(k3_subset_1('#skF_1', C_19), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', C_19), '#skF_1'))), inference(resolution, [status(thm)], [c_1384, c_20])).
% 6.83/2.56  tff(c_9067, plain, (![C_303]: (r1_tarski('#skF_2', C_303) | ~m1_subset_1(C_303, k1_zfmisc_1('#skF_1')) | ~r1_xboole_0(k3_subset_1('#skF_1', C_303), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', C_303), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1402])).
% 6.83/2.56  tff(c_9077, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_1') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1455, c_9067])).
% 6.83/2.56  tff(c_9096, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_441, c_24, c_9077])).
% 6.83/2.56  tff(c_9098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_319, c_9096])).
% 6.83/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.56  
% 6.83/2.56  Inference rules
% 6.83/2.56  ----------------------
% 6.83/2.56  #Ref     : 0
% 6.83/2.56  #Sup     : 2220
% 6.83/2.56  #Fact    : 0
% 6.83/2.56  #Define  : 0
% 6.83/2.56  #Split   : 7
% 6.83/2.56  #Chain   : 0
% 6.83/2.56  #Close   : 0
% 6.83/2.56  
% 6.83/2.56  Ordering : KBO
% 6.83/2.56  
% 6.83/2.56  Simplification rules
% 6.83/2.56  ----------------------
% 6.83/2.56  #Subsume      : 262
% 6.83/2.56  #Demod        : 1466
% 6.83/2.56  #Tautology    : 1298
% 6.83/2.56  #SimpNegUnit  : 6
% 6.83/2.56  #BackRed      : 0
% 6.83/2.56  
% 6.83/2.56  #Partial instantiations: 0
% 6.83/2.56  #Strategies tried      : 1
% 6.83/2.56  
% 6.83/2.56  Timing (in seconds)
% 6.83/2.56  ----------------------
% 6.83/2.56  Preprocessing        : 0.30
% 6.83/2.56  Parsing              : 0.16
% 6.83/2.56  CNF conversion       : 0.02
% 6.83/2.56  Main loop            : 1.47
% 6.83/2.56  Inferencing          : 0.41
% 6.83/2.56  Reduction            : 0.60
% 6.83/2.56  Demodulation         : 0.47
% 6.83/2.56  BG Simplification    : 0.05
% 6.83/2.56  Subsumption          : 0.31
% 6.83/2.56  Abstraction          : 0.06
% 6.83/2.56  MUC search           : 0.00
% 6.83/2.56  Cooper               : 0.00
% 6.83/2.56  Total                : 1.80
% 6.83/2.56  Index Insertion      : 0.00
% 6.83/2.56  Index Deletion       : 0.00
% 6.83/2.56  Index Matching       : 0.00
% 6.83/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
