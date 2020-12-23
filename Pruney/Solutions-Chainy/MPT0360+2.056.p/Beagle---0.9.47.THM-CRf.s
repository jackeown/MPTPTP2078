%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:26 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 125 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 204 expanded)
%              Number of equality atoms :   26 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_256,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k3_subset_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_260,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_256])).

tff(c_22,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_312,plain,(
    ! [A_66] :
      ( r1_xboole_0(A_66,'#skF_5')
      | ~ r1_tarski(A_66,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_22])).

tff(c_320,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_312])).

tff(c_28,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_72])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1010,plain,(
    ! [A_108,B_109,C_110] :
      ( ~ r2_hidden('#skF_1'(A_108,B_109,C_110),B_109)
      | r2_hidden('#skF_2'(A_108,B_109,C_110),C_110)
      | k4_xboole_0(A_108,B_109) = C_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1013,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_1010])).

tff(c_1021,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k3_xboole_0(A_1,k1_xboole_0) = C_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1013])).

tff(c_1024,plain,(
    ! [A_111,C_112] :
      ( r2_hidden('#skF_2'(A_111,A_111,C_112),C_112)
      | k3_xboole_0(A_111,k1_xboole_0) = C_112 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1013])).

tff(c_133,plain,(
    ! [D_37,B_38,A_39] :
      ( ~ r2_hidden(D_37,B_38)
      | ~ r2_hidden(D_37,k4_xboole_0(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_142,plain,(
    ! [D_37,A_13] :
      ( ~ r2_hidden(D_37,k1_xboole_0)
      | ~ r2_hidden(D_37,A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_133])).

tff(c_1083,plain,(
    ! [A_113,A_114] :
      ( ~ r2_hidden('#skF_2'(A_113,A_113,k1_xboole_0),A_114)
      | k3_xboole_0(A_113,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1024,c_142])).

tff(c_1102,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1021,c_1083])).

tff(c_1159,plain,(
    ! [A_117] : k4_xboole_0(A_117,A_117) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_87])).

tff(c_36,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(A_18,k4_xboole_0(B_19,C_20))
      | ~ r1_xboole_0(A_18,C_20)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1506,plain,(
    ! [A_135,A_136] :
      ( r1_tarski(A_135,k1_xboole_0)
      | ~ r1_xboole_0(A_135,A_136)
      | ~ r1_tarski(A_135,A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_36])).

tff(c_1518,plain,
    ( r1_tarski('#skF_4',k1_xboole_0)
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_320,c_1506])).

tff(c_1536,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1518])).

tff(c_26,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_xboole_0(A_42,C_43)
      | ~ r1_tarski(A_42,k4_xboole_0(B_44,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_159,plain,(
    ! [C_45] : r1_xboole_0(k1_xboole_0,C_45) ),
    inference(resolution,[status(thm)],[c_26,c_144])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_180,plain,(
    ! [C_49] : k4_xboole_0(k1_xboole_0,C_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_159,c_32])).

tff(c_287,plain,(
    ! [A_56,C_57] :
      ( r1_xboole_0(A_56,C_57)
      | ~ r1_tarski(A_56,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_22])).

tff(c_291,plain,(
    ! [A_56,C_57] :
      ( k4_xboole_0(A_56,C_57) = A_56
      | ~ r1_tarski(A_56,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_287,c_32])).

tff(c_1642,plain,(
    ! [C_142] : k4_xboole_0('#skF_4',C_142) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1536,c_291])).

tff(c_1115,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_87])).

tff(c_1647,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1642,c_1115])).

tff(c_1706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.53  
% 3.36/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.36/1.53  
% 3.36/1.53  %Foreground sorts:
% 3.36/1.53  
% 3.36/1.53  
% 3.36/1.53  %Background operators:
% 3.36/1.53  
% 3.36/1.53  
% 3.36/1.53  %Foreground operators:
% 3.36/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.36/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.36/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.53  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.36/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.36/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.36/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.53  
% 3.36/1.55  tff(f_72, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 3.36/1.55  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.36/1.55  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.36/1.55  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.36/1.55  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.36/1.55  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.36/1.55  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.36/1.55  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.55  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.36/1.55  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.55  tff(c_44, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.55  tff(c_42, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.55  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.55  tff(c_256, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k3_subset_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.55  tff(c_260, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_256])).
% 3.36/1.55  tff(c_22, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_tarski(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.55  tff(c_312, plain, (![A_66]: (r1_xboole_0(A_66, '#skF_5') | ~r1_tarski(A_66, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_260, c_22])).
% 3.36/1.55  tff(c_320, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_312])).
% 3.36/1.55  tff(c_28, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.55  tff(c_72, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.55  tff(c_87, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_72])).
% 3.36/1.55  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.55  tff(c_1010, plain, (![A_108, B_109, C_110]: (~r2_hidden('#skF_1'(A_108, B_109, C_110), B_109) | r2_hidden('#skF_2'(A_108, B_109, C_110), C_110) | k4_xboole_0(A_108, B_109)=C_110)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.55  tff(c_1013, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_1010])).
% 3.36/1.55  tff(c_1021, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k3_xboole_0(A_1, k1_xboole_0)=C_3)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1013])).
% 3.36/1.55  tff(c_1024, plain, (![A_111, C_112]: (r2_hidden('#skF_2'(A_111, A_111, C_112), C_112) | k3_xboole_0(A_111, k1_xboole_0)=C_112)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1013])).
% 3.36/1.55  tff(c_133, plain, (![D_37, B_38, A_39]: (~r2_hidden(D_37, B_38) | ~r2_hidden(D_37, k4_xboole_0(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.36/1.55  tff(c_142, plain, (![D_37, A_13]: (~r2_hidden(D_37, k1_xboole_0) | ~r2_hidden(D_37, A_13))), inference(superposition, [status(thm), theory('equality')], [c_28, c_133])).
% 3.36/1.55  tff(c_1083, plain, (![A_113, A_114]: (~r2_hidden('#skF_2'(A_113, A_113, k1_xboole_0), A_114) | k3_xboole_0(A_113, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1024, c_142])).
% 3.36/1.55  tff(c_1102, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1021, c_1083])).
% 3.36/1.55  tff(c_1159, plain, (![A_117]: (k4_xboole_0(A_117, A_117)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_87])).
% 3.36/1.55  tff(c_36, plain, (![A_18, B_19, C_20]: (r1_tarski(A_18, k4_xboole_0(B_19, C_20)) | ~r1_xboole_0(A_18, C_20) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.36/1.55  tff(c_1506, plain, (![A_135, A_136]: (r1_tarski(A_135, k1_xboole_0) | ~r1_xboole_0(A_135, A_136) | ~r1_tarski(A_135, A_136))), inference(superposition, [status(thm), theory('equality')], [c_1159, c_36])).
% 3.36/1.55  tff(c_1518, plain, (r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_320, c_1506])).
% 3.36/1.55  tff(c_1536, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1518])).
% 3.36/1.55  tff(c_26, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.55  tff(c_144, plain, (![A_42, C_43, B_44]: (r1_xboole_0(A_42, C_43) | ~r1_tarski(A_42, k4_xboole_0(B_44, C_43)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.55  tff(c_159, plain, (![C_45]: (r1_xboole_0(k1_xboole_0, C_45))), inference(resolution, [status(thm)], [c_26, c_144])).
% 3.36/1.55  tff(c_32, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.55  tff(c_180, plain, (![C_49]: (k4_xboole_0(k1_xboole_0, C_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_159, c_32])).
% 3.36/1.55  tff(c_287, plain, (![A_56, C_57]: (r1_xboole_0(A_56, C_57) | ~r1_tarski(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_180, c_22])).
% 3.36/1.55  tff(c_291, plain, (![A_56, C_57]: (k4_xboole_0(A_56, C_57)=A_56 | ~r1_tarski(A_56, k1_xboole_0))), inference(resolution, [status(thm)], [c_287, c_32])).
% 3.36/1.55  tff(c_1642, plain, (![C_142]: (k4_xboole_0('#skF_4', C_142)='#skF_4')), inference(resolution, [status(thm)], [c_1536, c_291])).
% 3.36/1.55  tff(c_1115, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_87])).
% 3.36/1.55  tff(c_1647, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1642, c_1115])).
% 3.36/1.55  tff(c_1706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1647])).
% 3.36/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.55  
% 3.36/1.55  Inference rules
% 3.36/1.55  ----------------------
% 3.36/1.55  #Ref     : 0
% 3.36/1.55  #Sup     : 401
% 3.36/1.55  #Fact    : 0
% 3.36/1.55  #Define  : 0
% 3.36/1.55  #Split   : 1
% 3.36/1.55  #Chain   : 0
% 3.36/1.55  #Close   : 0
% 3.36/1.55  
% 3.36/1.55  Ordering : KBO
% 3.36/1.55  
% 3.36/1.55  Simplification rules
% 3.36/1.55  ----------------------
% 3.36/1.55  #Subsume      : 56
% 3.36/1.55  #Demod        : 119
% 3.36/1.55  #Tautology    : 162
% 3.36/1.55  #SimpNegUnit  : 1
% 3.36/1.55  #BackRed      : 12
% 3.36/1.55  
% 3.36/1.55  #Partial instantiations: 0
% 3.36/1.55  #Strategies tried      : 1
% 3.36/1.55  
% 3.36/1.55  Timing (in seconds)
% 3.36/1.55  ----------------------
% 3.36/1.55  Preprocessing        : 0.30
% 3.36/1.55  Parsing              : 0.15
% 3.36/1.55  CNF conversion       : 0.02
% 3.36/1.55  Main loop            : 0.48
% 3.36/1.55  Inferencing          : 0.18
% 3.36/1.55  Reduction            : 0.14
% 3.36/1.55  Demodulation         : 0.11
% 3.36/1.55  BG Simplification    : 0.03
% 3.36/1.55  Subsumption          : 0.09
% 3.36/1.55  Abstraction          : 0.02
% 3.36/1.55  MUC search           : 0.00
% 3.36/1.55  Cooper               : 0.00
% 3.36/1.55  Total                : 0.81
% 3.36/1.55  Index Insertion      : 0.00
% 3.36/1.55  Index Deletion       : 0.00
% 3.36/1.55  Index Matching       : 0.00
% 3.36/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
