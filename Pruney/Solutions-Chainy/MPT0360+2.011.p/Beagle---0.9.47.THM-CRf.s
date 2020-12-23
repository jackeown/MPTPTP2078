%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:20 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   59 (  64 expanded)
%              Number of leaves         :   31 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :   55 (  71 expanded)
%              Number of equality atoms :   28 (  33 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_161,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_168,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_161])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_501,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = k3_subset_1(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_514,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_501])).

tff(c_20,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_546,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_20])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_169,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_161])).

tff(c_266,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_284,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_266])).

tff(c_301,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_284])).

tff(c_24,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_318,plain,(
    k5_xboole_0('#skF_5',k1_xboole_0) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_24])).

tff(c_330,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_318])).

tff(c_412,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_xboole_0(A_68,C_69)
      | ~ r1_xboole_0(A_68,k2_xboole_0(B_70,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_892,plain,(
    ! [A_84] :
      ( r1_xboole_0(A_84,'#skF_4')
      | ~ r1_xboole_0(A_84,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_412])).

tff(c_907,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_546,c_892])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_977,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_907,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1107,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_2])).

tff(c_1120,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1107])).

tff(c_1122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:12:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.57  
% 3.05/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.05/1.57  
% 3.05/1.57  %Foreground sorts:
% 3.05/1.57  
% 3.05/1.57  
% 3.05/1.57  %Background operators:
% 3.05/1.57  
% 3.05/1.57  
% 3.05/1.57  %Foreground operators:
% 3.05/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.05/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.05/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.57  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.05/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.05/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.05/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.05/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.05/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.05/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.05/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.57  
% 3.05/1.58  tff(f_97, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 3.05/1.58  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.05/1.58  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.05/1.58  tff(f_57, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.05/1.58  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.05/1.58  tff(f_59, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.05/1.58  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.05/1.58  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.05/1.58  tff(f_55, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.05/1.58  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.05/1.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.05/1.58  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.05/1.58  tff(c_52, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.05/1.58  tff(c_161, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.05/1.58  tff(c_168, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_52, c_161])).
% 3.05/1.58  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.05/1.58  tff(c_501, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=k3_subset_1(A_71, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.05/1.58  tff(c_514, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_501])).
% 3.05/1.58  tff(c_20, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.05/1.58  tff(c_546, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_514, c_20])).
% 3.05/1.58  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.05/1.58  tff(c_22, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.05/1.58  tff(c_54, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.05/1.58  tff(c_169, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_54, c_161])).
% 3.05/1.58  tff(c_266, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.58  tff(c_284, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_169, c_266])).
% 3.05/1.58  tff(c_301, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_284])).
% 3.05/1.58  tff(c_24, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.05/1.58  tff(c_318, plain, (k5_xboole_0('#skF_5', k1_xboole_0)=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_301, c_24])).
% 3.05/1.58  tff(c_330, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_318])).
% 3.05/1.58  tff(c_412, plain, (![A_68, C_69, B_70]: (r1_xboole_0(A_68, C_69) | ~r1_xboole_0(A_68, k2_xboole_0(B_70, C_69)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.05/1.58  tff(c_892, plain, (![A_84]: (r1_xboole_0(A_84, '#skF_4') | ~r1_xboole_0(A_84, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_330, c_412])).
% 3.05/1.58  tff(c_907, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_546, c_892])).
% 3.05/1.58  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.58  tff(c_977, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_907, c_4])).
% 3.05/1.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.58  tff(c_1107, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_977, c_2])).
% 3.05/1.58  tff(c_1120, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_1107])).
% 3.05/1.58  tff(c_1122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1120])).
% 3.05/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.58  
% 3.05/1.58  Inference rules
% 3.05/1.58  ----------------------
% 3.05/1.58  #Ref     : 0
% 3.05/1.58  #Sup     : 302
% 3.05/1.58  #Fact    : 0
% 3.05/1.58  #Define  : 0
% 3.05/1.58  #Split   : 0
% 3.05/1.58  #Chain   : 0
% 3.05/1.58  #Close   : 0
% 3.05/1.58  
% 3.05/1.58  Ordering : KBO
% 3.05/1.58  
% 3.05/1.58  Simplification rules
% 3.05/1.58  ----------------------
% 3.05/1.58  #Subsume      : 4
% 3.05/1.58  #Demod        : 114
% 3.05/1.58  #Tautology    : 199
% 3.05/1.58  #SimpNegUnit  : 3
% 3.05/1.58  #BackRed      : 0
% 3.05/1.58  
% 3.05/1.58  #Partial instantiations: 0
% 3.05/1.58  #Strategies tried      : 1
% 3.05/1.58  
% 3.05/1.58  Timing (in seconds)
% 3.05/1.58  ----------------------
% 3.05/1.58  Preprocessing        : 0.31
% 3.05/1.58  Parsing              : 0.16
% 3.05/1.58  CNF conversion       : 0.02
% 3.05/1.58  Main loop            : 0.39
% 3.05/1.58  Inferencing          : 0.14
% 3.05/1.58  Reduction            : 0.14
% 3.05/1.58  Demodulation         : 0.10
% 3.05/1.58  BG Simplification    : 0.02
% 3.05/1.58  Subsumption          : 0.07
% 3.05/1.58  Abstraction          : 0.01
% 3.05/1.58  MUC search           : 0.00
% 3.05/1.58  Cooper               : 0.00
% 3.05/1.58  Total                : 0.72
% 3.05/1.58  Index Insertion      : 0.00
% 3.05/1.58  Index Deletion       : 0.00
% 3.05/1.59  Index Matching       : 0.00
% 3.05/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
