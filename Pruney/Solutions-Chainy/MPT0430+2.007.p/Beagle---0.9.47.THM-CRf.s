%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:12 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   56 (  79 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 137 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ( v3_setfam_1(B,A)
                & r1_tarski(C,B) )
             => v3_setfam_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_38,plain,(
    v3_setfam_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_198,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden(A_54,B_55)
      | ~ v3_setfam_1(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_201,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_setfam_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_198])).

tff(c_207,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_201])).

tff(c_34,plain,(
    ~ v3_setfam_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_76,plain,(
    ! [B_41,A_42] :
      ( v3_setfam_1(B_41,A_42)
      | r2_hidden(A_42,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_82,plain,
    ( v3_setfam_1('#skF_5','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_76])).

tff(c_87,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_82])).

tff(c_24,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_53,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_tarski(A_33,C_34)
      | ~ r1_tarski(B_35,C_34)
      | ~ r1_tarski(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,'#skF_4')
      | ~ r1_tarski(A_36,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_65,plain,(
    ! [B_12] : r1_tarski(k4_xboole_0('#skF_5',B_12),'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_60])).

tff(c_28,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_47,plain,(
    ! [B_28,A_29] :
      ( ~ r1_xboole_0(B_28,A_29)
      | ~ r1_tarski(B_28,A_29)
      | v1_xboole_0(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_118,plain,(
    ! [A_50,B_51] :
      ( ~ r1_tarski(k4_xboole_0(A_50,B_51),B_51)
      | v1_xboole_0(k4_xboole_0(A_50,B_51)) ) ),
    inference(resolution,[status(thm)],[c_28,c_47])).

tff(c_137,plain,(
    v1_xboole_0(k4_xboole_0('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_65,c_118])).

tff(c_20,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_20])).

tff(c_298,plain,(
    ! [D_59,A_60,B_61] :
      ( r2_hidden(D_59,k4_xboole_0(A_60,B_61))
      | r2_hidden(D_59,B_61)
      | ~ r2_hidden(D_59,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1109,plain,(
    ! [D_111] :
      ( r2_hidden(D_111,k1_xboole_0)
      | r2_hidden(D_111,'#skF_4')
      | ~ r2_hidden(D_111,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_298])).

tff(c_139,plain,(
    ! [A_52] : v1_xboole_0(k4_xboole_0(A_52,A_52)) ),
    inference(resolution,[status(thm)],[c_24,c_118])).

tff(c_149,plain,(
    ! [A_53] : k4_xboole_0(A_53,A_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_468,plain,(
    ! [D_68,A_69] :
      ( ~ r2_hidden(D_68,A_69)
      | ~ r2_hidden(D_68,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_4])).

tff(c_474,plain,(
    ~ r2_hidden('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_87,c_468])).

tff(c_1124,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_1109,c_474])).

tff(c_1133,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1124])).

tff(c_1135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_1133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:38:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.51  
% 2.88/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.51  %$ v3_setfam_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.88/1.51  
% 2.88/1.51  %Foreground sorts:
% 2.88/1.51  
% 2.88/1.51  
% 2.88/1.51  %Background operators:
% 2.88/1.51  
% 2.88/1.51  
% 2.88/1.51  %Foreground operators:
% 2.88/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.88/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.88/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.51  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 2.88/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.88/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.51  
% 3.08/1.53  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_setfam_1)).
% 3.08/1.53  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_setfam_1)).
% 3.08/1.53  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.08/1.53  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.08/1.53  tff(f_57, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.08/1.53  tff(f_55, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.08/1.53  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.08/1.53  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.08/1.53  tff(c_38, plain, (v3_setfam_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.53  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.53  tff(c_198, plain, (![A_54, B_55]: (~r2_hidden(A_54, B_55) | ~v3_setfam_1(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.08/1.53  tff(c_201, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v3_setfam_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_198])).
% 3.08/1.53  tff(c_207, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_201])).
% 3.08/1.53  tff(c_34, plain, (~v3_setfam_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.53  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.53  tff(c_76, plain, (![B_41, A_42]: (v3_setfam_1(B_41, A_42) | r2_hidden(A_42, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.08/1.53  tff(c_82, plain, (v3_setfam_1('#skF_5', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_76])).
% 3.08/1.53  tff(c_87, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_34, c_82])).
% 3.08/1.53  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.08/1.53  tff(c_36, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.08/1.53  tff(c_53, plain, (![A_33, C_34, B_35]: (r1_tarski(A_33, C_34) | ~r1_tarski(B_35, C_34) | ~r1_tarski(A_33, B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.08/1.53  tff(c_60, plain, (![A_36]: (r1_tarski(A_36, '#skF_4') | ~r1_tarski(A_36, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_53])).
% 3.08/1.53  tff(c_65, plain, (![B_12]: (r1_tarski(k4_xboole_0('#skF_5', B_12), '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_60])).
% 3.08/1.53  tff(c_28, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.53  tff(c_47, plain, (![B_28, A_29]: (~r1_xboole_0(B_28, A_29) | ~r1_tarski(B_28, A_29) | v1_xboole_0(B_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.08/1.53  tff(c_118, plain, (![A_50, B_51]: (~r1_tarski(k4_xboole_0(A_50, B_51), B_51) | v1_xboole_0(k4_xboole_0(A_50, B_51)))), inference(resolution, [status(thm)], [c_28, c_47])).
% 3.08/1.53  tff(c_137, plain, (v1_xboole_0(k4_xboole_0('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_65, c_118])).
% 3.08/1.53  tff(c_20, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.08/1.53  tff(c_147, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_20])).
% 3.08/1.53  tff(c_298, plain, (![D_59, A_60, B_61]: (r2_hidden(D_59, k4_xboole_0(A_60, B_61)) | r2_hidden(D_59, B_61) | ~r2_hidden(D_59, A_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.08/1.53  tff(c_1109, plain, (![D_111]: (r2_hidden(D_111, k1_xboole_0) | r2_hidden(D_111, '#skF_4') | ~r2_hidden(D_111, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_298])).
% 3.08/1.53  tff(c_139, plain, (![A_52]: (v1_xboole_0(k4_xboole_0(A_52, A_52)))), inference(resolution, [status(thm)], [c_24, c_118])).
% 3.08/1.53  tff(c_149, plain, (![A_53]: (k4_xboole_0(A_53, A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_139, c_20])).
% 3.08/1.53  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.08/1.53  tff(c_468, plain, (![D_68, A_69]: (~r2_hidden(D_68, A_69) | ~r2_hidden(D_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_149, c_4])).
% 3.08/1.53  tff(c_474, plain, (~r2_hidden('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_87, c_468])).
% 3.08/1.53  tff(c_1124, plain, (r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_1109, c_474])).
% 3.08/1.53  tff(c_1133, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1124])).
% 3.08/1.53  tff(c_1135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_1133])).
% 3.08/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.53  
% 3.08/1.53  Inference rules
% 3.08/1.53  ----------------------
% 3.08/1.53  #Ref     : 0
% 3.08/1.53  #Sup     : 261
% 3.08/1.53  #Fact    : 0
% 3.08/1.53  #Define  : 0
% 3.08/1.53  #Split   : 0
% 3.08/1.53  #Chain   : 0
% 3.08/1.53  #Close   : 0
% 3.08/1.53  
% 3.08/1.53  Ordering : KBO
% 3.08/1.53  
% 3.08/1.53  Simplification rules
% 3.08/1.53  ----------------------
% 3.08/1.53  #Subsume      : 29
% 3.08/1.53  #Demod        : 248
% 3.08/1.53  #Tautology    : 173
% 3.08/1.53  #SimpNegUnit  : 2
% 3.08/1.53  #BackRed      : 9
% 3.08/1.53  
% 3.08/1.53  #Partial instantiations: 0
% 3.08/1.53  #Strategies tried      : 1
% 3.08/1.53  
% 3.08/1.53  Timing (in seconds)
% 3.08/1.53  ----------------------
% 3.08/1.53  Preprocessing        : 0.30
% 3.08/1.53  Parsing              : 0.16
% 3.08/1.53  CNF conversion       : 0.02
% 3.08/1.53  Main loop            : 0.42
% 3.08/1.53  Inferencing          : 0.16
% 3.08/1.53  Reduction            : 0.13
% 3.08/1.53  Demodulation         : 0.10
% 3.08/1.53  BG Simplification    : 0.02
% 3.08/1.53  Subsumption          : 0.07
% 3.08/1.53  Abstraction          : 0.02
% 3.08/1.53  MUC search           : 0.00
% 3.08/1.53  Cooper               : 0.00
% 3.08/1.53  Total                : 0.75
% 3.08/1.53  Index Insertion      : 0.00
% 3.08/1.53  Index Deletion       : 0.00
% 3.08/1.53  Index Matching       : 0.00
% 3.08/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
