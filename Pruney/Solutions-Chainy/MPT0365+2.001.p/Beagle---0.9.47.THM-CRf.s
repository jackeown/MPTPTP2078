%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:42 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 111 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  103 ( 255 expanded)
%              Number of equality atoms :   15 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [B_10,A_9,C_12] :
      ( r1_tarski(B_10,k3_subset_1(A_9,C_12))
      | ~ r1_xboole_0(B_10,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k3_subset_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_161,plain,(
    ! [B_32,C_33,A_34] :
      ( r1_xboole_0(B_32,C_33)
      | ~ r1_tarski(B_32,k3_subset_1(A_34,C_33))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_362,plain,(
    ! [A_48,C_49] :
      ( r1_xboole_0(k3_subset_1(A_48,C_49),C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_48))
      | ~ m1_subset_1(k3_subset_1(A_48,C_49),k1_zfmisc_1(A_48)) ) ),
    inference(resolution,[status(thm)],[c_12,c_161])).

tff(c_369,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(k3_subset_1(A_7,B_8),B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_14,c_362])).

tff(c_69,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_81,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_2])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [B_35,A_36,C_37] :
      ( r1_tarski(B_35,k3_subset_1(A_36,C_37))
      | ~ r1_xboole_0(B_35,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_136,plain,(
    ! [B_29,C_30,A_31] :
      ( r1_tarski(B_29,C_30)
      | ~ r1_xboole_0(B_29,k3_subset_1(A_31,C_30))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(A_31))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_139,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_136])).

tff(c_146,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_139])).

tff(c_148,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_151,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_151])).

tff(c_156,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,
    ( k3_subset_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_156,c_8])).

tff(c_167,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_171,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_168,c_167])).

tff(c_179,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_171])).

tff(c_184,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_184])).

tff(c_189,plain,(
    k3_subset_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_22,plain,(
    ! [B_14,C_16,A_13] :
      ( r1_tarski(B_14,C_16)
      | ~ r1_xboole_0(B_14,k3_subset_1(A_13,C_16))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_204,plain,(
    ! [B_14] :
      ( r1_tarski(B_14,'#skF_2')
      | ~ r1_xboole_0(B_14,'#skF_3')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_14,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_22])).

tff(c_297,plain,(
    ! [B_45] :
      ( r1_tarski(B_45,'#skF_2')
      | ~ r1_xboole_0(B_45,'#skF_3')
      | ~ m1_subset_1(B_45,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_204])).

tff(c_421,plain,(
    ! [B_56] :
      ( r1_tarski(k3_subset_1('#skF_1',B_56),'#skF_2')
      | ~ r1_xboole_0(k3_subset_1('#skF_1',B_56),'#skF_3')
      | ~ m1_subset_1(B_56,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_297])).

tff(c_428,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_369,c_421])).

tff(c_438,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_428])).

tff(c_445,plain,
    ( k3_subset_1('#skF_1','#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_438,c_8])).

tff(c_448,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_445])).

tff(c_451,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_448])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 10:07:16 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.42  
% 2.44/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.43  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.44/1.43  
% 2.44/1.43  %Foreground sorts:
% 2.44/1.43  
% 2.44/1.43  
% 2.44/1.43  %Background operators:
% 2.44/1.43  
% 2.44/1.43  
% 2.44/1.43  %Foreground operators:
% 2.44/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.44/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.44/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.43  
% 2.44/1.45  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_subset_1)).
% 2.44/1.45  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.44/1.45  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.44/1.45  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.44/1.45  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.44/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.44/1.45  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 2.44/1.45  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.45  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.45  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.45  tff(c_18, plain, (![B_10, A_9, C_12]: (r1_tarski(B_10, k3_subset_1(A_9, C_12)) | ~r1_xboole_0(B_10, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.45  tff(c_24, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.45  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(k3_subset_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.44/1.45  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.44/1.45  tff(c_161, plain, (![B_32, C_33, A_34]: (r1_xboole_0(B_32, C_33) | ~r1_tarski(B_32, k3_subset_1(A_34, C_33)) | ~m1_subset_1(C_33, k1_zfmisc_1(A_34)) | ~m1_subset_1(B_32, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.45  tff(c_362, plain, (![A_48, C_49]: (r1_xboole_0(k3_subset_1(A_48, C_49), C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_48)) | ~m1_subset_1(k3_subset_1(A_48, C_49), k1_zfmisc_1(A_48)))), inference(resolution, [status(thm)], [c_12, c_161])).
% 2.44/1.45  tff(c_369, plain, (![A_7, B_8]: (r1_xboole_0(k3_subset_1(A_7, B_8), B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_14, c_362])).
% 2.44/1.45  tff(c_69, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.45  tff(c_77, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_69])).
% 2.44/1.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.44/1.45  tff(c_81, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_77, c_2])).
% 2.44/1.45  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.45  tff(c_168, plain, (![B_35, A_36, C_37]: (r1_tarski(B_35, k3_subset_1(A_36, C_37)) | ~r1_xboole_0(B_35, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(A_36)) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.45  tff(c_26, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.45  tff(c_136, plain, (![B_29, C_30, A_31]: (r1_tarski(B_29, C_30) | ~r1_xboole_0(B_29, k3_subset_1(A_31, C_30)) | ~m1_subset_1(C_30, k1_zfmisc_1(A_31)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.45  tff(c_139, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_136])).
% 2.44/1.45  tff(c_146, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_139])).
% 2.44/1.45  tff(c_148, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_146])).
% 2.44/1.45  tff(c_151, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_148])).
% 2.44/1.45  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_151])).
% 2.44/1.45  tff(c_156, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_146])).
% 2.44/1.45  tff(c_8, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.44/1.45  tff(c_160, plain, (k3_subset_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_156, c_8])).
% 2.44/1.45  tff(c_167, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_160])).
% 2.44/1.45  tff(c_171, plain, (~r1_xboole_0('#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_168, c_167])).
% 2.44/1.45  tff(c_179, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_171])).
% 2.44/1.45  tff(c_184, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_179])).
% 2.44/1.45  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_184])).
% 2.44/1.45  tff(c_189, plain, (k3_subset_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_160])).
% 2.44/1.45  tff(c_22, plain, (![B_14, C_16, A_13]: (r1_tarski(B_14, C_16) | ~r1_xboole_0(B_14, k3_subset_1(A_13, C_16)) | ~m1_subset_1(C_16, k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.45  tff(c_204, plain, (![B_14]: (r1_tarski(B_14, '#skF_2') | ~r1_xboole_0(B_14, '#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_14, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_189, c_22])).
% 2.44/1.45  tff(c_297, plain, (![B_45]: (r1_tarski(B_45, '#skF_2') | ~r1_xboole_0(B_45, '#skF_3') | ~m1_subset_1(B_45, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_204])).
% 2.44/1.45  tff(c_421, plain, (![B_56]: (r1_tarski(k3_subset_1('#skF_1', B_56), '#skF_2') | ~r1_xboole_0(k3_subset_1('#skF_1', B_56), '#skF_3') | ~m1_subset_1(B_56, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_297])).
% 2.44/1.45  tff(c_428, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_369, c_421])).
% 2.44/1.45  tff(c_438, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_428])).
% 2.44/1.45  tff(c_445, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_438, c_8])).
% 2.44/1.45  tff(c_448, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_24, c_445])).
% 2.44/1.45  tff(c_451, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_448])).
% 2.44/1.45  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_451])).
% 2.44/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.45  
% 2.44/1.45  Inference rules
% 2.44/1.45  ----------------------
% 2.44/1.45  #Ref     : 0
% 2.44/1.45  #Sup     : 91
% 2.44/1.45  #Fact    : 0
% 2.44/1.45  #Define  : 0
% 2.44/1.45  #Split   : 4
% 2.44/1.45  #Chain   : 0
% 2.44/1.45  #Close   : 0
% 2.44/1.45  
% 2.44/1.45  Ordering : KBO
% 2.44/1.45  
% 2.44/1.45  Simplification rules
% 2.44/1.45  ----------------------
% 2.44/1.45  #Subsume      : 3
% 2.44/1.45  #Demod        : 67
% 2.44/1.45  #Tautology    : 54
% 2.44/1.45  #SimpNegUnit  : 5
% 2.44/1.45  #BackRed      : 5
% 2.44/1.45  
% 2.44/1.45  #Partial instantiations: 0
% 2.44/1.45  #Strategies tried      : 1
% 2.44/1.45  
% 2.44/1.45  Timing (in seconds)
% 2.44/1.45  ----------------------
% 2.44/1.45  Preprocessing        : 0.33
% 2.44/1.45  Parsing              : 0.19
% 2.44/1.45  CNF conversion       : 0.02
% 2.44/1.45  Main loop            : 0.32
% 2.44/1.45  Inferencing          : 0.11
% 2.44/1.45  Reduction            : 0.10
% 2.44/1.45  Demodulation         : 0.08
% 2.44/1.45  BG Simplification    : 0.02
% 2.44/1.45  Subsumption          : 0.07
% 2.44/1.45  Abstraction          : 0.01
% 2.44/1.45  MUC search           : 0.00
% 2.44/1.45  Cooper               : 0.00
% 2.44/1.45  Total                : 0.69
% 2.44/1.45  Index Insertion      : 0.00
% 2.44/1.45  Index Deletion       : 0.00
% 2.44/1.45  Index Matching       : 0.00
% 2.44/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
