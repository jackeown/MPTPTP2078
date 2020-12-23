%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:28 EST 2020

% Result     : Theorem 7.22s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 234 expanded)
%              Number of leaves         :   19 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 363 expanded)
%              Number of equality atoms :   48 ( 247 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] : k4_xboole_0(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A,C),B),k2_zfmisc_1(A,k4_xboole_0(B,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_4983,plain,(
    ! [A_699,B_700] :
      ( r1_tarski(A_699,B_700)
      | k4_xboole_0(A_699,B_700) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_74,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_93,plain,(
    k4_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_89,c_74])).

tff(c_40,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_122,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_122])).

tff(c_898,plain,(
    ! [A_85,C_86,B_87,D_88] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_85,C_86),B_87),k2_zfmisc_1(A_85,k4_xboole_0(B_87,D_88))) = k4_xboole_0(k2_zfmisc_1(A_85,B_87),k2_zfmisc_1(C_86,D_88)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4242,plain,(
    ! [A_683,C_684,B_685,D_686] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(A_683,C_684),B_685),k4_xboole_0(k2_zfmisc_1(A_683,B_685),k2_zfmisc_1(C_684,D_686))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_12])).

tff(c_4367,plain,(
    k4_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_4242])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4462,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_10])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4591,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4462,c_14])).

tff(c_4640,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_4591])).

tff(c_16,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4679,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4640,c_4640,c_16])).

tff(c_38,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4682,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4640,c_38])).

tff(c_4966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4679,c_4682])).

tff(c_4967,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_4987,plain,(
    k4_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4983,c_4967])).

tff(c_18,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5795,plain,(
    ! [A_747,C_748,B_749,D_750] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_747,C_748),B_749),k2_zfmisc_1(A_747,k4_xboole_0(B_749,D_750))) = k4_xboole_0(k2_zfmisc_1(A_747,B_749),k2_zfmisc_1(C_748,D_750)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5876,plain,(
    ! [A_747,C_748,A_6] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_747,C_748),A_6),k2_zfmisc_1(A_747,A_6)) = k4_xboole_0(k2_zfmisc_1(A_747,A_6),k2_zfmisc_1(C_748,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_5795])).

tff(c_7037,plain,(
    ! [A_780,C_781,A_782] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_780,C_781),A_782),k2_zfmisc_1(A_780,A_782)) = k2_zfmisc_1(A_780,A_782) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16,c_5876])).

tff(c_7113,plain,(
    ! [A_782,A_7] : k2_xboole_0(k2_zfmisc_1(k1_xboole_0,A_782),k2_zfmisc_1(A_7,A_782)) = k2_zfmisc_1(A_7,A_782) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7037])).

tff(c_7142,plain,(
    ! [A_7,A_782] : k2_xboole_0(k1_xboole_0,k2_zfmisc_1(A_7,A_782)) = k2_zfmisc_1(A_7,A_782) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7113])).

tff(c_4968,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_5016,plain,(
    ! [A_705,B_706] :
      ( k4_xboole_0(A_705,B_706) = k1_xboole_0
      | ~ r1_tarski(A_705,B_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5031,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4968,c_5016])).

tff(c_5853,plain,(
    ! [B_749,D_750] : k2_xboole_0(k2_zfmisc_1(k1_xboole_0,B_749),k2_zfmisc_1('#skF_1',k4_xboole_0(B_749,D_750))) = k4_xboole_0(k2_zfmisc_1('#skF_1',B_749),k2_zfmisc_1('#skF_3',D_750)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5031,c_5795])).

tff(c_5889,plain,(
    ! [B_749,D_750] : k4_xboole_0(k2_zfmisc_1('#skF_1',B_749),k2_zfmisc_1('#skF_3',D_750)) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1('#skF_1',k4_xboole_0(B_749,D_750))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5853])).

tff(c_11224,plain,(
    ! [B_1448,D_1449] : k4_xboole_0(k2_zfmisc_1('#skF_1',B_1448),k2_zfmisc_1('#skF_3',D_1449)) = k2_zfmisc_1('#skF_1',k4_xboole_0(B_1448,D_1449)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7142,c_5889])).

tff(c_5029,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_5016])).

tff(c_11281,plain,(
    k2_zfmisc_1('#skF_1',k4_xboole_0('#skF_2','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11224,c_5029])).

tff(c_11472,plain,
    ( k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11281,c_14])).

tff(c_11524,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_4987,c_11472])).

tff(c_11573,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_1',B_10) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11524,c_11524,c_18])).

tff(c_11575,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11524,c_38])).

tff(c_11739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11573,c_11575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.22/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.67  
% 7.47/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.67  %$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.47/2.67  
% 7.47/2.67  %Foreground sorts:
% 7.47/2.67  
% 7.47/2.67  
% 7.47/2.67  %Background operators:
% 7.47/2.67  
% 7.47/2.67  
% 7.47/2.67  %Foreground operators:
% 7.47/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.47/2.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.47/2.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.47/2.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.47/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.47/2.67  tff('#skF_2', type, '#skF_2': $i).
% 7.47/2.67  tff('#skF_3', type, '#skF_3': $i).
% 7.47/2.67  tff('#skF_1', type, '#skF_1': $i).
% 7.47/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.47/2.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.47/2.67  tff('#skF_4', type, '#skF_4': $i).
% 7.47/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.47/2.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.47/2.67  
% 7.55/2.68  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.55/2.68  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 7.55/2.68  tff(f_64, axiom, (![A, B, C, D]: (k4_xboole_0(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A, C), B), k2_zfmisc_1(A, k4_xboole_0(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_zfmisc_1)).
% 7.55/2.68  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.55/2.68  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.55/2.68  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.55/2.68  tff(c_4983, plain, (![A_699, B_700]: (r1_tarski(A_699, B_700) | k4_xboole_0(A_699, B_700)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.55/2.68  tff(c_89, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.55/2.68  tff(c_36, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.55/2.68  tff(c_74, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 7.55/2.68  tff(c_93, plain, (k4_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_89, c_74])).
% 7.55/2.68  tff(c_40, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.55/2.68  tff(c_122, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.55/2.68  tff(c_133, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_122])).
% 7.55/2.68  tff(c_898, plain, (![A_85, C_86, B_87, D_88]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_85, C_86), B_87), k2_zfmisc_1(A_85, k4_xboole_0(B_87, D_88)))=k4_xboole_0(k2_zfmisc_1(A_85, B_87), k2_zfmisc_1(C_86, D_88)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.55/2.68  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.55/2.68  tff(c_4242, plain, (![A_683, C_684, B_685, D_686]: (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(A_683, C_684), B_685), k4_xboole_0(k2_zfmisc_1(A_683, B_685), k2_zfmisc_1(C_684, D_686)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_898, c_12])).
% 7.55/2.68  tff(c_4367, plain, (k4_xboole_0(k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_133, c_4242])).
% 7.55/2.68  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.55/2.68  tff(c_4462, plain, (k2_zfmisc_1(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4367, c_10])).
% 7.55/2.68  tff(c_14, plain, (![B_10, A_9]: (k1_xboole_0=B_10 | k1_xboole_0=A_9 | k2_zfmisc_1(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.55/2.68  tff(c_4591, plain, (k1_xboole_0='#skF_2' | k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4462, c_14])).
% 7.55/2.68  tff(c_4640, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_93, c_4591])).
% 7.55/2.68  tff(c_16, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.55/2.68  tff(c_4679, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4640, c_4640, c_16])).
% 7.55/2.68  tff(c_38, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.55/2.68  tff(c_4682, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4640, c_38])).
% 7.55/2.68  tff(c_4966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4679, c_4682])).
% 7.55/2.68  tff(c_4967, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 7.55/2.68  tff(c_4987, plain, (k4_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4983, c_4967])).
% 7.55/2.68  tff(c_18, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.55/2.68  tff(c_5795, plain, (![A_747, C_748, B_749, D_750]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_747, C_748), B_749), k2_zfmisc_1(A_747, k4_xboole_0(B_749, D_750)))=k4_xboole_0(k2_zfmisc_1(A_747, B_749), k2_zfmisc_1(C_748, D_750)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.55/2.68  tff(c_5876, plain, (![A_747, C_748, A_6]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_747, C_748), A_6), k2_zfmisc_1(A_747, A_6))=k4_xboole_0(k2_zfmisc_1(A_747, A_6), k2_zfmisc_1(C_748, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_5795])).
% 7.55/2.68  tff(c_7037, plain, (![A_780, C_781, A_782]: (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(A_780, C_781), A_782), k2_zfmisc_1(A_780, A_782))=k2_zfmisc_1(A_780, A_782))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16, c_5876])).
% 7.55/2.68  tff(c_7113, plain, (![A_782, A_7]: (k2_xboole_0(k2_zfmisc_1(k1_xboole_0, A_782), k2_zfmisc_1(A_7, A_782))=k2_zfmisc_1(A_7, A_782))), inference(superposition, [status(thm), theory('equality')], [c_12, c_7037])).
% 7.55/2.68  tff(c_7142, plain, (![A_7, A_782]: (k2_xboole_0(k1_xboole_0, k2_zfmisc_1(A_7, A_782))=k2_zfmisc_1(A_7, A_782))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7113])).
% 7.55/2.68  tff(c_4968, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 7.55/2.68  tff(c_5016, plain, (![A_705, B_706]: (k4_xboole_0(A_705, B_706)=k1_xboole_0 | ~r1_tarski(A_705, B_706))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.55/2.68  tff(c_5031, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_4968, c_5016])).
% 7.55/2.68  tff(c_5853, plain, (![B_749, D_750]: (k2_xboole_0(k2_zfmisc_1(k1_xboole_0, B_749), k2_zfmisc_1('#skF_1', k4_xboole_0(B_749, D_750)))=k4_xboole_0(k2_zfmisc_1('#skF_1', B_749), k2_zfmisc_1('#skF_3', D_750)))), inference(superposition, [status(thm), theory('equality')], [c_5031, c_5795])).
% 7.55/2.68  tff(c_5889, plain, (![B_749, D_750]: (k4_xboole_0(k2_zfmisc_1('#skF_1', B_749), k2_zfmisc_1('#skF_3', D_750))=k2_xboole_0(k1_xboole_0, k2_zfmisc_1('#skF_1', k4_xboole_0(B_749, D_750))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_5853])).
% 7.55/2.68  tff(c_11224, plain, (![B_1448, D_1449]: (k4_xboole_0(k2_zfmisc_1('#skF_1', B_1448), k2_zfmisc_1('#skF_3', D_1449))=k2_zfmisc_1('#skF_1', k4_xboole_0(B_1448, D_1449)))), inference(demodulation, [status(thm), theory('equality')], [c_7142, c_5889])).
% 7.55/2.68  tff(c_5029, plain, (k4_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_5016])).
% 7.55/2.68  tff(c_11281, plain, (k2_zfmisc_1('#skF_1', k4_xboole_0('#skF_2', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11224, c_5029])).
% 7.55/2.68  tff(c_11472, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11281, c_14])).
% 7.55/2.68  tff(c_11524, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_4987, c_11472])).
% 7.55/2.68  tff(c_11573, plain, (![B_10]: (k2_zfmisc_1('#skF_1', B_10)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11524, c_11524, c_18])).
% 7.55/2.68  tff(c_11575, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11524, c_38])).
% 7.55/2.68  tff(c_11739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11573, c_11575])).
% 7.55/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/2.68  
% 7.55/2.68  Inference rules
% 7.55/2.68  ----------------------
% 7.55/2.68  #Ref     : 0
% 7.55/2.68  #Sup     : 3087
% 7.55/2.68  #Fact    : 0
% 7.55/2.68  #Define  : 0
% 7.55/2.68  #Split   : 8
% 7.55/2.68  #Chain   : 0
% 7.55/2.68  #Close   : 0
% 7.55/2.68  
% 7.55/2.68  Ordering : KBO
% 7.55/2.68  
% 7.55/2.68  Simplification rules
% 7.55/2.68  ----------------------
% 7.55/2.68  #Subsume      : 292
% 7.55/2.68  #Demod        : 2747
% 7.55/2.68  #Tautology    : 1214
% 7.55/2.68  #SimpNegUnit  : 17
% 7.55/2.68  #BackRed      : 121
% 7.55/2.68  
% 7.55/2.68  #Partial instantiations: 624
% 7.55/2.68  #Strategies tried      : 1
% 7.55/2.68  
% 7.55/2.68  Timing (in seconds)
% 7.55/2.68  ----------------------
% 7.55/2.68  Preprocessing        : 0.32
% 7.55/2.68  Parsing              : 0.17
% 7.55/2.68  CNF conversion       : 0.02
% 7.55/2.68  Main loop            : 1.54
% 7.55/2.68  Inferencing          : 0.47
% 7.55/2.68  Reduction            : 0.65
% 7.55/2.68  Demodulation         : 0.52
% 7.55/2.68  BG Simplification    : 0.07
% 7.55/2.68  Subsumption          : 0.24
% 7.55/2.68  Abstraction          : 0.10
% 7.55/2.68  MUC search           : 0.00
% 7.55/2.68  Cooper               : 0.00
% 7.55/2.68  Total                : 1.89
% 7.55/2.68  Index Insertion      : 0.00
% 7.55/2.68  Index Deletion       : 0.00
% 7.55/2.68  Index Matching       : 0.00
% 7.55/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
