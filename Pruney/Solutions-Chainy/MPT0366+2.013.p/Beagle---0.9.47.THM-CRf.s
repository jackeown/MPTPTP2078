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
% DateTime   : Thu Dec  3 09:56:45 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 129 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  107 ( 257 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    ! [A_41,B_42] :
      ( ~ r1_xboole_0(A_41,B_42)
      | k3_xboole_0(A_41,B_42) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_71])).

tff(c_90,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,(
    ! [C_7] :
      ( ~ r1_xboole_0('#skF_5','#skF_6')
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_6])).

tff(c_113,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_109])).

tff(c_32,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    ! [A_46] : k3_xboole_0(A_46,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_77])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_143,plain,(
    ! [A_46] : k5_xboole_0(A_46,k1_xboole_0) = k4_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_10])).

tff(c_150,plain,(
    ! [A_46] : k5_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_143])).

tff(c_106,plain,(
    k5_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_10])).

tff(c_194,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_106])).

tff(c_12,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_tarski(A_12,k4_xboole_0(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_252,plain,(
    ! [A_56] :
      ( r1_xboole_0(A_56,'#skF_6')
      | ~ r1_tarski(A_56,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_12])).

tff(c_76,plain,(
    ! [A_38,B_39] :
      ( ~ r1_xboole_0(A_38,B_39)
      | k3_xboole_0(A_38,B_39) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_71])).

tff(c_285,plain,(
    ! [A_62] :
      ( k3_xboole_0(A_62,'#skF_6') = k1_xboole_0
      | ~ r1_tarski(A_62,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_252,c_76])).

tff(c_289,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_285])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_318,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_6'),k1_xboole_0)
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_4])).

tff(c_327,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_318])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k3_subset_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_430,plain,(
    ! [A_81,B_82] :
      ( k3_subset_1(A_81,k3_subset_1(A_81,B_82)) = B_82
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_440,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_430])).

tff(c_467,plain,(
    ! [B_83,A_84,C_85] :
      ( r1_xboole_0(B_83,k3_subset_1(A_84,C_85))
      | ~ r1_tarski(B_83,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_611,plain,(
    ! [A_93,C_94,B_95] :
      ( r1_xboole_0(k3_subset_1(A_93,C_94),B_95)
      | ~ r1_tarski(B_95,C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(A_93))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_93)) ) ),
    inference(resolution,[status(thm)],[c_467,c_2])).

tff(c_632,plain,(
    ! [B_95] :
      ( r1_xboole_0('#skF_6',B_95)
      | ~ r1_tarski(B_95,k3_subset_1('#skF_3','#skF_6'))
      | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_6'),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_611])).

tff(c_1387,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3','#skF_6'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_632])).

tff(c_1390,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_1387])).

tff(c_1394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1390])).

tff(c_1396,plain,(
    m1_subset_1(k3_subset_1('#skF_3','#skF_6'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_545,plain,(
    ! [B_88,C_89,A_90] :
      ( r1_tarski(B_88,C_89)
      | ~ r1_xboole_0(B_88,k3_subset_1(A_90,C_89))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_560,plain,(
    ! [B_88] :
      ( r1_tarski(B_88,k3_subset_1('#skF_3','#skF_6'))
      | ~ r1_xboole_0(B_88,'#skF_6')
      | ~ m1_subset_1(k3_subset_1('#skF_3','#skF_6'),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(B_88,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_545])).

tff(c_1786,plain,(
    ! [B_146] :
      ( r1_tarski(B_146,k3_subset_1('#skF_3','#skF_6'))
      | ~ r1_xboole_0(B_146,'#skF_6')
      | ~ m1_subset_1(B_146,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_560])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1803,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1786,c_28])).

tff(c_1812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_327,c_1803])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:33:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.66  
% 3.70/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.70/1.67  
% 3.70/1.67  %Foreground sorts:
% 3.70/1.67  
% 3.70/1.67  
% 3.70/1.67  %Background operators:
% 3.70/1.67  
% 3.70/1.67  
% 3.70/1.67  %Foreground operators:
% 3.70/1.67  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.70/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.70/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.70/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.67  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.70/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.70/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.70/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.70/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.70/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.70/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.67  
% 3.97/1.68  tff(f_95, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 3.97/1.68  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.97/1.68  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.97/1.68  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.97/1.68  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.97/1.68  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.97/1.68  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.97/1.68  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.97/1.68  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.97/1.68  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.97/1.68  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 3.97/1.68  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.97/1.68  tff(c_30, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.97/1.68  tff(c_50, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.97/1.68  tff(c_56, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_30, c_50])).
% 3.97/1.68  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.97/1.68  tff(c_71, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.97/1.68  tff(c_77, plain, (![A_41, B_42]: (~r1_xboole_0(A_41, B_42) | k3_xboole_0(A_41, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_71])).
% 3.97/1.68  tff(c_90, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_77])).
% 3.97/1.68  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.97/1.68  tff(c_109, plain, (![C_7]: (~r1_xboole_0('#skF_5', '#skF_6') | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_90, c_6])).
% 3.97/1.68  tff(c_113, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_109])).
% 3.97/1.68  tff(c_32, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.97/1.68  tff(c_16, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.97/1.68  tff(c_18, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.68  tff(c_138, plain, (![A_46]: (k3_xboole_0(A_46, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_77])).
% 3.97/1.68  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.97/1.68  tff(c_143, plain, (![A_46]: (k5_xboole_0(A_46, k1_xboole_0)=k4_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_138, c_10])).
% 3.97/1.68  tff(c_150, plain, (![A_46]: (k5_xboole_0(A_46, k1_xboole_0)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_143])).
% 3.97/1.68  tff(c_106, plain, (k5_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_90, c_10])).
% 3.97/1.68  tff(c_194, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_106])).
% 3.97/1.68  tff(c_12, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_tarski(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.97/1.68  tff(c_252, plain, (![A_56]: (r1_xboole_0(A_56, '#skF_6') | ~r1_tarski(A_56, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_194, c_12])).
% 3.97/1.68  tff(c_76, plain, (![A_38, B_39]: (~r1_xboole_0(A_38, B_39) | k3_xboole_0(A_38, B_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_71])).
% 3.97/1.68  tff(c_285, plain, (![A_62]: (k3_xboole_0(A_62, '#skF_6')=k1_xboole_0 | ~r1_tarski(A_62, '#skF_5'))), inference(resolution, [status(thm)], [c_252, c_76])).
% 3.97/1.68  tff(c_289, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_285])).
% 3.97/1.68  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.97/1.68  tff(c_318, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_6'), k1_xboole_0) | r1_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_289, c_4])).
% 3.97/1.68  tff(c_327, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_113, c_318])).
% 3.97/1.68  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.97/1.68  tff(c_20, plain, (![A_17, B_18]: (m1_subset_1(k3_subset_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.97/1.68  tff(c_430, plain, (![A_81, B_82]: (k3_subset_1(A_81, k3_subset_1(A_81, B_82))=B_82 | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.97/1.68  tff(c_440, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_34, c_430])).
% 3.97/1.68  tff(c_467, plain, (![B_83, A_84, C_85]: (r1_xboole_0(B_83, k3_subset_1(A_84, C_85)) | ~r1_tarski(B_83, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.97/1.68  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.97/1.68  tff(c_611, plain, (![A_93, C_94, B_95]: (r1_xboole_0(k3_subset_1(A_93, C_94), B_95) | ~r1_tarski(B_95, C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(A_93)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_93)))), inference(resolution, [status(thm)], [c_467, c_2])).
% 3.97/1.68  tff(c_632, plain, (![B_95]: (r1_xboole_0('#skF_6', B_95) | ~r1_tarski(B_95, k3_subset_1('#skF_3', '#skF_6')) | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_6'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(B_95, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_440, c_611])).
% 3.97/1.68  tff(c_1387, plain, (~m1_subset_1(k3_subset_1('#skF_3', '#skF_6'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_632])).
% 3.97/1.68  tff(c_1390, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_1387])).
% 3.97/1.68  tff(c_1394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1390])).
% 3.97/1.68  tff(c_1396, plain, (m1_subset_1(k3_subset_1('#skF_3', '#skF_6'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_632])).
% 3.97/1.68  tff(c_545, plain, (![B_88, C_89, A_90]: (r1_tarski(B_88, C_89) | ~r1_xboole_0(B_88, k3_subset_1(A_90, C_89)) | ~m1_subset_1(C_89, k1_zfmisc_1(A_90)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.97/1.68  tff(c_560, plain, (![B_88]: (r1_tarski(B_88, k3_subset_1('#skF_3', '#skF_6')) | ~r1_xboole_0(B_88, '#skF_6') | ~m1_subset_1(k3_subset_1('#skF_3', '#skF_6'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(B_88, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_440, c_545])).
% 3.97/1.68  tff(c_1786, plain, (![B_146]: (r1_tarski(B_146, k3_subset_1('#skF_3', '#skF_6')) | ~r1_xboole_0(B_146, '#skF_6') | ~m1_subset_1(B_146, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_560])).
% 3.97/1.68  tff(c_28, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.97/1.68  tff(c_1803, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_1786, c_28])).
% 3.97/1.68  tff(c_1812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_327, c_1803])).
% 3.97/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.68  
% 3.97/1.68  Inference rules
% 3.97/1.68  ----------------------
% 3.97/1.68  #Ref     : 0
% 3.97/1.68  #Sup     : 418
% 3.97/1.68  #Fact    : 0
% 3.97/1.68  #Define  : 0
% 3.97/1.68  #Split   : 29
% 3.97/1.68  #Chain   : 0
% 3.97/1.68  #Close   : 0
% 3.97/1.68  
% 3.97/1.68  Ordering : KBO
% 3.97/1.68  
% 3.97/1.68  Simplification rules
% 3.97/1.68  ----------------------
% 3.97/1.68  #Subsume      : 126
% 3.97/1.68  #Demod        : 114
% 3.97/1.68  #Tautology    : 125
% 3.97/1.68  #SimpNegUnit  : 12
% 3.97/1.68  #BackRed      : 1
% 3.97/1.68  
% 3.97/1.68  #Partial instantiations: 0
% 3.97/1.68  #Strategies tried      : 1
% 3.97/1.68  
% 3.97/1.68  Timing (in seconds)
% 3.97/1.68  ----------------------
% 3.97/1.68  Preprocessing        : 0.28
% 3.97/1.69  Parsing              : 0.16
% 3.97/1.69  CNF conversion       : 0.02
% 3.97/1.69  Main loop            : 0.59
% 3.97/1.69  Inferencing          : 0.21
% 3.97/1.69  Reduction            : 0.18
% 3.97/1.69  Demodulation         : 0.12
% 3.97/1.69  BG Simplification    : 0.02
% 3.97/1.69  Subsumption          : 0.13
% 3.97/1.69  Abstraction          : 0.02
% 3.97/1.69  MUC search           : 0.00
% 3.97/1.69  Cooper               : 0.00
% 3.97/1.69  Total                : 0.91
% 3.97/1.69  Index Insertion      : 0.00
% 3.97/1.69  Index Deletion       : 0.00
% 3.97/1.69  Index Matching       : 0.00
% 3.97/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
