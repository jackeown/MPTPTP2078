%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:44 EST 2020

% Result     : Theorem 6.44s
% Output     : CNFRefutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 123 expanded)
%              Number of leaves         :   25 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 251 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_575,plain,(
    ! [A_95,B_96] :
      ( k3_subset_1(A_95,k3_subset_1(A_95,B_96)) = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_587,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_575])).

tff(c_619,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1(k3_subset_1(A_103,B_104),k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k3_subset_1(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4009,plain,(
    ! [A_220,B_221] :
      ( k4_xboole_0(A_220,k3_subset_1(A_220,B_221)) = k3_subset_1(A_220,k3_subset_1(A_220,B_221))
      | ~ m1_subset_1(B_221,k1_zfmisc_1(A_220)) ) ),
    inference(resolution,[status(thm)],[c_619,c_28])).

tff(c_4021,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_4009])).

tff(c_4032,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_4021])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden('#skF_1'(A_53,B_54),B_54)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_118,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,B_57)
      | ~ r1_tarski(A_56,k4_xboole_0(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    ! [B_57,C_58] : r1_tarski(k4_xboole_0(B_57,C_58),B_57) ),
    inference(resolution,[status(thm)],[c_105,c_118])).

tff(c_4269,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4032,c_126])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_449,plain,(
    ! [A_93,B_94] :
      ( k4_xboole_0(A_93,B_94) = k3_subset_1(A_93,B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_464,plain,(
    k4_xboole_0('#skF_2','#skF_5') = k3_subset_1('#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_449])).

tff(c_868,plain,(
    ! [A_111,B_112,C_113] :
      ( r1_tarski(A_111,k4_xboole_0(B_112,C_113))
      | ~ r1_xboole_0(A_111,C_113)
      | ~ r1_tarski(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4284,plain,(
    ! [A_224] :
      ( r1_tarski(A_224,k3_subset_1('#skF_2','#skF_5'))
      | ~ r1_xboole_0(A_224,'#skF_5')
      | ~ r1_tarski(A_224,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_868])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4315,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4284,c_40])).

tff(c_4370,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4269,c_4315])).

tff(c_586,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_575])).

tff(c_4019,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_5')) = k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_5')) ),
    inference(resolution,[status(thm)],[c_46,c_4009])).

tff(c_4030,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_4019])).

tff(c_4065,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4030,c_126])).

tff(c_42,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_588,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_575])).

tff(c_4023,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_4009])).

tff(c_4034,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_4023])).

tff(c_106,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,(
    ! [B_7,C_8] : r1_xboole_0(k4_xboole_0(B_7,C_8),C_8) ),
    inference(resolution,[status(thm)],[c_106,c_8])).

tff(c_4134,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4034,c_117])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4165,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4134,c_14])).

tff(c_466,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_449])).

tff(c_44,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(A_15,k4_xboole_0(B_16,C_17))
      | ~ r1_xboole_0(A_15,C_17)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1012,plain,(
    ! [A_124,C_125,B_126,D_127] :
      ( r1_xboole_0(A_124,C_125)
      | ~ r1_xboole_0(B_126,D_127)
      | ~ r1_tarski(C_125,D_127)
      | ~ r1_tarski(A_124,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2930,plain,(
    ! [A_197,C_198,B_199,A_200] :
      ( r1_xboole_0(A_197,C_198)
      | ~ r1_tarski(C_198,B_199)
      | ~ r1_tarski(A_197,A_200)
      | k4_xboole_0(A_200,B_199) != A_200 ) ),
    inference(resolution,[status(thm)],[c_16,c_1012])).

tff(c_6611,plain,(
    ! [A_285,A_287,A_286,C_283,B_284] :
      ( r1_xboole_0(A_287,A_285)
      | ~ r1_tarski(A_287,A_286)
      | k4_xboole_0(A_286,k4_xboole_0(B_284,C_283)) != A_286
      | ~ r1_xboole_0(A_285,C_283)
      | ~ r1_tarski(A_285,B_284) ) ),
    inference(resolution,[status(thm)],[c_18,c_2930])).

tff(c_6709,plain,(
    ! [A_288,B_289,C_290] :
      ( r1_xboole_0('#skF_3',A_288)
      | k4_xboole_0('#skF_4',k4_xboole_0(B_289,C_290)) != '#skF_4'
      | ~ r1_xboole_0(A_288,C_290)
      | ~ r1_tarski(A_288,B_289) ) ),
    inference(resolution,[status(thm)],[c_44,c_6611])).

tff(c_6761,plain,(
    ! [A_288] :
      ( r1_xboole_0('#skF_3',A_288)
      | k4_xboole_0('#skF_4',k3_subset_1('#skF_2','#skF_4')) != '#skF_4'
      | ~ r1_xboole_0(A_288,'#skF_4')
      | ~ r1_tarski(A_288,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_6709])).

tff(c_7217,plain,(
    ! [A_293] :
      ( r1_xboole_0('#skF_3',A_293)
      | ~ r1_xboole_0(A_293,'#skF_4')
      | ~ r1_tarski(A_293,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4165,c_6761])).

tff(c_7277,plain,
    ( r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_7217])).

tff(c_7329,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4065,c_7277])).

tff(c_7331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4370,c_7329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.44/2.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.44/2.39  
% 6.44/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.44/2.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.44/2.39  
% 6.44/2.39  %Foreground sorts:
% 6.44/2.39  
% 6.44/2.39  
% 6.44/2.39  %Background operators:
% 6.44/2.39  
% 6.44/2.39  
% 6.44/2.39  %Foreground operators:
% 6.44/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.44/2.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.44/2.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.44/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.44/2.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.44/2.39  tff('#skF_5', type, '#skF_5': $i).
% 6.44/2.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.44/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.44/2.39  tff('#skF_3', type, '#skF_3': $i).
% 6.44/2.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.44/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.44/2.39  tff('#skF_4', type, '#skF_4': $i).
% 6.44/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.44/2.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.44/2.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.44/2.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.44/2.39  
% 6.52/2.41  tff(f_108, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 6.52/2.41  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.52/2.41  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.52/2.41  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.52/2.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.52/2.41  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.52/2.41  tff(f_56, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 6.52/2.41  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.52/2.41  tff(f_46, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 6.52/2.41  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.52/2.41  tff(c_575, plain, (![A_95, B_96]: (k3_subset_1(A_95, k3_subset_1(A_95, B_96))=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.52/2.41  tff(c_587, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_50, c_575])).
% 6.52/2.41  tff(c_619, plain, (![A_103, B_104]: (m1_subset_1(k3_subset_1(A_103, B_104), k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.52/2.41  tff(c_28, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k3_subset_1(A_20, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.52/2.41  tff(c_4009, plain, (![A_220, B_221]: (k4_xboole_0(A_220, k3_subset_1(A_220, B_221))=k3_subset_1(A_220, k3_subset_1(A_220, B_221)) | ~m1_subset_1(B_221, k1_zfmisc_1(A_220)))), inference(resolution, [status(thm)], [c_619, c_28])).
% 6.52/2.41  tff(c_4021, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_4009])).
% 6.52/2.41  tff(c_4032, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_587, c_4021])).
% 6.52/2.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.52/2.41  tff(c_100, plain, (![A_53, B_54]: (~r2_hidden('#skF_1'(A_53, B_54), B_54) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.52/2.41  tff(c_105, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_100])).
% 6.52/2.41  tff(c_118, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, B_57) | ~r1_tarski(A_56, k4_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.52/2.41  tff(c_126, plain, (![B_57, C_58]: (r1_tarski(k4_xboole_0(B_57, C_58), B_57))), inference(resolution, [status(thm)], [c_105, c_118])).
% 6.52/2.41  tff(c_4269, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4032, c_126])).
% 6.52/2.41  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.52/2.41  tff(c_449, plain, (![A_93, B_94]: (k4_xboole_0(A_93, B_94)=k3_subset_1(A_93, B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.52/2.41  tff(c_464, plain, (k4_xboole_0('#skF_2', '#skF_5')=k3_subset_1('#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_449])).
% 6.52/2.41  tff(c_868, plain, (![A_111, B_112, C_113]: (r1_tarski(A_111, k4_xboole_0(B_112, C_113)) | ~r1_xboole_0(A_111, C_113) | ~r1_tarski(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.52/2.41  tff(c_4284, plain, (![A_224]: (r1_tarski(A_224, k3_subset_1('#skF_2', '#skF_5')) | ~r1_xboole_0(A_224, '#skF_5') | ~r1_tarski(A_224, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_464, c_868])).
% 6.52/2.41  tff(c_40, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.52/2.41  tff(c_4315, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4284, c_40])).
% 6.52/2.41  tff(c_4370, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4269, c_4315])).
% 6.52/2.41  tff(c_586, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_46, c_575])).
% 6.52/2.41  tff(c_4019, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_5'))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_4009])).
% 6.52/2.41  tff(c_4030, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_586, c_4019])).
% 6.52/2.41  tff(c_4065, plain, (r1_tarski('#skF_5', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4030, c_126])).
% 6.52/2.41  tff(c_42, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.52/2.41  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.52/2.41  tff(c_588, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_48, c_575])).
% 6.52/2.41  tff(c_4023, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_4009])).
% 6.52/2.41  tff(c_4034, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_588, c_4023])).
% 6.52/2.41  tff(c_106, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_6, c_100])).
% 6.52/2.41  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_tarski(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.52/2.41  tff(c_117, plain, (![B_7, C_8]: (r1_xboole_0(k4_xboole_0(B_7, C_8), C_8))), inference(resolution, [status(thm)], [c_106, c_8])).
% 6.52/2.41  tff(c_4134, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4034, c_117])).
% 6.52/2.41  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.52/2.41  tff(c_4165, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_4134, c_14])).
% 6.52/2.41  tff(c_466, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_449])).
% 6.52/2.41  tff(c_44, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.52/2.41  tff(c_18, plain, (![A_15, B_16, C_17]: (r1_tarski(A_15, k4_xboole_0(B_16, C_17)) | ~r1_xboole_0(A_15, C_17) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.52/2.41  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k4_xboole_0(A_13, B_14)!=A_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.52/2.41  tff(c_1012, plain, (![A_124, C_125, B_126, D_127]: (r1_xboole_0(A_124, C_125) | ~r1_xboole_0(B_126, D_127) | ~r1_tarski(C_125, D_127) | ~r1_tarski(A_124, B_126))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.52/2.41  tff(c_2930, plain, (![A_197, C_198, B_199, A_200]: (r1_xboole_0(A_197, C_198) | ~r1_tarski(C_198, B_199) | ~r1_tarski(A_197, A_200) | k4_xboole_0(A_200, B_199)!=A_200)), inference(resolution, [status(thm)], [c_16, c_1012])).
% 6.52/2.41  tff(c_6611, plain, (![A_285, A_287, A_286, C_283, B_284]: (r1_xboole_0(A_287, A_285) | ~r1_tarski(A_287, A_286) | k4_xboole_0(A_286, k4_xboole_0(B_284, C_283))!=A_286 | ~r1_xboole_0(A_285, C_283) | ~r1_tarski(A_285, B_284))), inference(resolution, [status(thm)], [c_18, c_2930])).
% 6.52/2.41  tff(c_6709, plain, (![A_288, B_289, C_290]: (r1_xboole_0('#skF_3', A_288) | k4_xboole_0('#skF_4', k4_xboole_0(B_289, C_290))!='#skF_4' | ~r1_xboole_0(A_288, C_290) | ~r1_tarski(A_288, B_289))), inference(resolution, [status(thm)], [c_44, c_6611])).
% 6.52/2.41  tff(c_6761, plain, (![A_288]: (r1_xboole_0('#skF_3', A_288) | k4_xboole_0('#skF_4', k3_subset_1('#skF_2', '#skF_4'))!='#skF_4' | ~r1_xboole_0(A_288, '#skF_4') | ~r1_tarski(A_288, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_466, c_6709])).
% 6.52/2.41  tff(c_7217, plain, (![A_293]: (r1_xboole_0('#skF_3', A_293) | ~r1_xboole_0(A_293, '#skF_4') | ~r1_tarski(A_293, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4165, c_6761])).
% 6.52/2.41  tff(c_7277, plain, (r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_7217])).
% 6.52/2.41  tff(c_7329, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4065, c_7277])).
% 6.52/2.41  tff(c_7331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4370, c_7329])).
% 6.52/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.41  
% 6.52/2.41  Inference rules
% 6.52/2.41  ----------------------
% 6.52/2.41  #Ref     : 0
% 6.52/2.41  #Sup     : 1848
% 6.52/2.41  #Fact    : 0
% 6.52/2.41  #Define  : 0
% 6.52/2.41  #Split   : 12
% 6.52/2.41  #Chain   : 0
% 6.52/2.41  #Close   : 0
% 6.52/2.41  
% 6.52/2.41  Ordering : KBO
% 6.52/2.41  
% 6.52/2.41  Simplification rules
% 6.52/2.41  ----------------------
% 6.52/2.41  #Subsume      : 277
% 6.52/2.41  #Demod        : 971
% 6.52/2.41  #Tautology    : 794
% 6.52/2.41  #SimpNegUnit  : 15
% 6.52/2.41  #BackRed      : 0
% 6.52/2.41  
% 6.52/2.41  #Partial instantiations: 0
% 6.52/2.41  #Strategies tried      : 1
% 6.52/2.41  
% 6.52/2.41  Timing (in seconds)
% 6.52/2.41  ----------------------
% 6.52/2.41  Preprocessing        : 0.32
% 6.52/2.41  Parsing              : 0.17
% 6.52/2.41  CNF conversion       : 0.02
% 6.52/2.41  Main loop            : 1.33
% 6.52/2.41  Inferencing          : 0.38
% 6.52/2.41  Reduction            : 0.54
% 6.52/2.41  Demodulation         : 0.41
% 6.52/2.41  BG Simplification    : 0.04
% 6.52/2.41  Subsumption          : 0.29
% 6.52/2.41  Abstraction          : 0.05
% 6.52/2.41  MUC search           : 0.00
% 6.52/2.41  Cooper               : 0.00
% 6.52/2.41  Total                : 1.68
% 6.52/2.41  Index Insertion      : 0.00
% 6.52/2.41  Index Deletion       : 0.00
% 6.52/2.41  Index Matching       : 0.00
% 6.52/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
