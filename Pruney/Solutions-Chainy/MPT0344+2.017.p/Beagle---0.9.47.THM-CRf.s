%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:21 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 212 expanded)
%              Number of leaves         :   23 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  152 ( 509 expanded)
%              Number of equality atoms :   16 (  69 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_52,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_105,plain,(
    ! [B_36,A_37] :
      ( r2_hidden(B_36,A_37)
      | ~ m1_subset_1(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [C_19] :
      ( ~ r2_hidden(C_19,'#skF_5')
      | ~ m1_subset_1(C_19,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_120,plain,(
    ! [B_36] :
      ( ~ m1_subset_1(B_36,'#skF_4')
      | ~ m1_subset_1(B_36,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_105,c_28])).

tff(c_191,plain,(
    ! [B_51] :
      ( ~ m1_subset_1(B_51,'#skF_4')
      | ~ m1_subset_1(B_51,'#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_201,plain,(
    ! [B_16] :
      ( ~ m1_subset_1(B_16,'#skF_4')
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_191])).

tff(c_202,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_55,plain,(
    ! [C_27] :
      ( ~ r2_hidden(C_27,'#skF_5')
      | ~ m1_subset_1(C_27,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_63,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12,c_55])).

tff(c_67,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_63])).

tff(c_161,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(B_48,A_49)
      | ~ r2_hidden(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_177,plain,(
    ! [A_10] :
      ( m1_subset_1('#skF_3'(A_10),A_10)
      | v1_xboole_0(A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(resolution,[status(thm)],[c_12,c_161])).

tff(c_74,plain,(
    ! [B_30,A_31] :
      ( m1_subset_1(B_30,A_31)
      | ~ v1_xboole_0(B_30)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_86,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_67])).

tff(c_87,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_14] : k3_tarski(k1_zfmisc_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,k3_tarski(B_33))
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_91,plain,(
    ! [A_32,A_14] :
      ( r1_tarski(A_32,A_14)
      | ~ r2_hidden(A_32,k1_zfmisc_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_88])).

tff(c_109,plain,(
    ! [B_36,A_14] :
      ( r1_tarski(B_36,A_14)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_105,c_91])).

tff(c_123,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(B_39,A_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_109])).

tff(c_132,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_123])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r2_hidden(B_16,A_15)
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_226,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_855,plain,(
    ! [B_110,B_111,A_112] :
      ( r2_hidden(B_110,B_111)
      | ~ r1_tarski(A_112,B_111)
      | ~ m1_subset_1(B_110,A_112)
      | v1_xboole_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_20,c_226])).

tff(c_869,plain,(
    ! [B_110] :
      ( r2_hidden(B_110,'#skF_4')
      | ~ m1_subset_1(B_110,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_132,c_855])).

tff(c_886,plain,(
    ! [B_113] :
      ( r2_hidden(B_113,'#skF_4')
      | ~ m1_subset_1(B_113,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_869])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( m1_subset_1(B_16,A_15)
      | ~ r2_hidden(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_891,plain,(
    ! [B_113] :
      ( m1_subset_1(B_113,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_113,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_886,c_18])).

tff(c_905,plain,(
    ! [B_114] :
      ( m1_subset_1(B_114,'#skF_4')
      | ~ m1_subset_1(B_114,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_891])).

tff(c_913,plain,
    ( m1_subset_1('#skF_3'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_177,c_905])).

tff(c_928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_202,c_67,c_913])).

tff(c_930,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_44,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_3'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_933,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_930,c_48])).

tff(c_937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_933])).

tff(c_939,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_943,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_939,c_48])).

tff(c_946,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_30])).

tff(c_1029,plain,(
    ! [B_132,A_133] :
      ( r2_hidden(B_132,A_133)
      | ~ m1_subset_1(B_132,A_133)
      | v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1053,plain,(
    ! [B_132] :
      ( ~ m1_subset_1(B_132,'#skF_4')
      | ~ m1_subset_1(B_132,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1029,c_28])).

tff(c_1080,plain,(
    ! [B_137] :
      ( ~ m1_subset_1(B_137,'#skF_4')
      | ~ m1_subset_1(B_137,'#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_1053])).

tff(c_1090,plain,(
    ! [B_16] :
      ( ~ m1_subset_1(B_16,'#skF_4')
      | ~ v1_xboole_0(B_16)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_1080])).

tff(c_1092,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1090])).

tff(c_959,plain,(
    ! [A_116,B_117] :
      ( r1_tarski(A_116,k3_tarski(B_117))
      | ~ r2_hidden(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_962,plain,(
    ! [A_116,A_14] :
      ( r1_tarski(A_116,A_14)
      | ~ r2_hidden(A_116,k1_zfmisc_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_959])).

tff(c_1040,plain,(
    ! [B_132,A_14] :
      ( r1_tarski(B_132,A_14)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_1029,c_962])).

tff(c_1055,plain,(
    ! [B_134,A_135] :
      ( r1_tarski(B_134,A_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_135)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1040])).

tff(c_1071,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1055])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1094,plain,(
    ! [C_140,B_141,A_142] :
      ( r2_hidden(C_140,B_141)
      | ~ r2_hidden(C_140,A_142)
      | ~ r1_tarski(A_142,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1124,plain,(
    ! [A_144,B_145] :
      ( r2_hidden('#skF_1'(A_144),B_145)
      | ~ r1_tarski(A_144,B_145)
      | v1_xboole_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_4,c_1094])).

tff(c_1146,plain,(
    ! [B_146,A_147] :
      ( ~ v1_xboole_0(B_146)
      | ~ r1_tarski(A_147,B_146)
      | v1_xboole_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_1124,c_2])).

tff(c_1152,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1071,c_1146])).

tff(c_1168,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_1152])).

tff(c_1170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1092,c_1168])).

tff(c_1172,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1090])).

tff(c_944,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(A_24)
      | A_24 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_48])).

tff(c_1175,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1172,c_944])).

tff(c_1179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_946,c_1175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:58:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.49  
% 3.13/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 3.13/1.50  
% 3.13/1.50  %Foreground sorts:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Background operators:
% 3.13/1.50  
% 3.13/1.50  
% 3.13/1.50  %Foreground operators:
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.13/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.13/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.50  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.13/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.50  
% 3.13/1.52  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 3.13/1.52  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.13/1.52  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.13/1.52  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.13/1.52  tff(f_52, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.13/1.52  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.13/1.52  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.13/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.13/1.52  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.13/1.52  tff(c_22, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~v1_xboole_0(B_16) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.52  tff(c_105, plain, (![B_36, A_37]: (r2_hidden(B_36, A_37) | ~m1_subset_1(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.52  tff(c_28, plain, (![C_19]: (~r2_hidden(C_19, '#skF_5') | ~m1_subset_1(C_19, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.13/1.52  tff(c_120, plain, (![B_36]: (~m1_subset_1(B_36, '#skF_4') | ~m1_subset_1(B_36, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_105, c_28])).
% 3.13/1.52  tff(c_191, plain, (![B_51]: (~m1_subset_1(B_51, '#skF_4') | ~m1_subset_1(B_51, '#skF_5'))), inference(splitLeft, [status(thm)], [c_120])).
% 3.13/1.52  tff(c_201, plain, (![B_16]: (~m1_subset_1(B_16, '#skF_4') | ~v1_xboole_0(B_16) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_22, c_191])).
% 3.13/1.52  tff(c_202, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_201])).
% 3.13/1.52  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.13/1.52  tff(c_55, plain, (![C_27]: (~r2_hidden(C_27, '#skF_5') | ~m1_subset_1(C_27, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.13/1.52  tff(c_63, plain, (~m1_subset_1('#skF_3'('#skF_5'), '#skF_4') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_12, c_55])).
% 3.13/1.52  tff(c_67, plain, (~m1_subset_1('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_63])).
% 3.13/1.52  tff(c_161, plain, (![B_48, A_49]: (m1_subset_1(B_48, A_49) | ~r2_hidden(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.52  tff(c_177, plain, (![A_10]: (m1_subset_1('#skF_3'(A_10), A_10) | v1_xboole_0(A_10) | k1_xboole_0=A_10)), inference(resolution, [status(thm)], [c_12, c_161])).
% 3.13/1.52  tff(c_74, plain, (![B_30, A_31]: (m1_subset_1(B_30, A_31) | ~v1_xboole_0(B_30) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.52  tff(c_86, plain, (~v1_xboole_0('#skF_3'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_74, c_67])).
% 3.13/1.52  tff(c_87, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_86])).
% 3.13/1.52  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.13/1.52  tff(c_26, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.52  tff(c_16, plain, (![A_14]: (k3_tarski(k1_zfmisc_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.13/1.52  tff(c_88, plain, (![A_32, B_33]: (r1_tarski(A_32, k3_tarski(B_33)) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.52  tff(c_91, plain, (![A_32, A_14]: (r1_tarski(A_32, A_14) | ~r2_hidden(A_32, k1_zfmisc_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_88])).
% 3.13/1.52  tff(c_109, plain, (![B_36, A_14]: (r1_tarski(B_36, A_14) | ~m1_subset_1(B_36, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_105, c_91])).
% 3.13/1.52  tff(c_123, plain, (![B_39, A_40]: (r1_tarski(B_39, A_40) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)))), inference(negUnitSimplification, [status(thm)], [c_26, c_109])).
% 3.13/1.52  tff(c_132, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_123])).
% 3.13/1.52  tff(c_20, plain, (![B_16, A_15]: (r2_hidden(B_16, A_15) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.52  tff(c_226, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.13/1.52  tff(c_855, plain, (![B_110, B_111, A_112]: (r2_hidden(B_110, B_111) | ~r1_tarski(A_112, B_111) | ~m1_subset_1(B_110, A_112) | v1_xboole_0(A_112))), inference(resolution, [status(thm)], [c_20, c_226])).
% 3.13/1.52  tff(c_869, plain, (![B_110]: (r2_hidden(B_110, '#skF_4') | ~m1_subset_1(B_110, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_132, c_855])).
% 3.13/1.52  tff(c_886, plain, (![B_113]: (r2_hidden(B_113, '#skF_4') | ~m1_subset_1(B_113, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_202, c_869])).
% 3.13/1.52  tff(c_18, plain, (![B_16, A_15]: (m1_subset_1(B_16, A_15) | ~r2_hidden(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.52  tff(c_891, plain, (![B_113]: (m1_subset_1(B_113, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_113, '#skF_5'))), inference(resolution, [status(thm)], [c_886, c_18])).
% 3.13/1.52  tff(c_905, plain, (![B_114]: (m1_subset_1(B_114, '#skF_4') | ~m1_subset_1(B_114, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_87, c_891])).
% 3.13/1.52  tff(c_913, plain, (m1_subset_1('#skF_3'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_177, c_905])).
% 3.13/1.52  tff(c_928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_202, c_67, c_913])).
% 3.13/1.52  tff(c_930, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_201])).
% 3.13/1.52  tff(c_44, plain, (![A_24]: (r2_hidden('#skF_3'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.13/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.52  tff(c_48, plain, (![A_24]: (~v1_xboole_0(A_24) | k1_xboole_0=A_24)), inference(resolution, [status(thm)], [c_44, c_2])).
% 3.13/1.52  tff(c_933, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_930, c_48])).
% 3.13/1.52  tff(c_937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_933])).
% 3.13/1.52  tff(c_939, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_86])).
% 3.13/1.52  tff(c_943, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_939, c_48])).
% 3.13/1.52  tff(c_946, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_943, c_30])).
% 3.13/1.52  tff(c_1029, plain, (![B_132, A_133]: (r2_hidden(B_132, A_133) | ~m1_subset_1(B_132, A_133) | v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.13/1.52  tff(c_1053, plain, (![B_132]: (~m1_subset_1(B_132, '#skF_4') | ~m1_subset_1(B_132, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_1029, c_28])).
% 3.13/1.52  tff(c_1080, plain, (![B_137]: (~m1_subset_1(B_137, '#skF_4') | ~m1_subset_1(B_137, '#skF_5'))), inference(splitLeft, [status(thm)], [c_1053])).
% 3.13/1.52  tff(c_1090, plain, (![B_16]: (~m1_subset_1(B_16, '#skF_4') | ~v1_xboole_0(B_16) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_22, c_1080])).
% 3.13/1.52  tff(c_1092, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1090])).
% 3.13/1.52  tff(c_959, plain, (![A_116, B_117]: (r1_tarski(A_116, k3_tarski(B_117)) | ~r2_hidden(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.13/1.52  tff(c_962, plain, (![A_116, A_14]: (r1_tarski(A_116, A_14) | ~r2_hidden(A_116, k1_zfmisc_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_959])).
% 3.13/1.52  tff(c_1040, plain, (![B_132, A_14]: (r1_tarski(B_132, A_14) | ~m1_subset_1(B_132, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_1029, c_962])).
% 3.13/1.52  tff(c_1055, plain, (![B_134, A_135]: (r1_tarski(B_134, A_135) | ~m1_subset_1(B_134, k1_zfmisc_1(A_135)))), inference(negUnitSimplification, [status(thm)], [c_26, c_1040])).
% 3.13/1.52  tff(c_1071, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_1055])).
% 3.13/1.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.13/1.52  tff(c_1094, plain, (![C_140, B_141, A_142]: (r2_hidden(C_140, B_141) | ~r2_hidden(C_140, A_142) | ~r1_tarski(A_142, B_141))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.13/1.52  tff(c_1124, plain, (![A_144, B_145]: (r2_hidden('#skF_1'(A_144), B_145) | ~r1_tarski(A_144, B_145) | v1_xboole_0(A_144))), inference(resolution, [status(thm)], [c_4, c_1094])).
% 3.13/1.52  tff(c_1146, plain, (![B_146, A_147]: (~v1_xboole_0(B_146) | ~r1_tarski(A_147, B_146) | v1_xboole_0(A_147))), inference(resolution, [status(thm)], [c_1124, c_2])).
% 3.13/1.52  tff(c_1152, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1071, c_1146])).
% 3.13/1.52  tff(c_1168, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_939, c_1152])).
% 3.13/1.52  tff(c_1170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1092, c_1168])).
% 3.13/1.52  tff(c_1172, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1090])).
% 3.13/1.52  tff(c_944, plain, (![A_24]: (~v1_xboole_0(A_24) | A_24='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_943, c_48])).
% 3.13/1.52  tff(c_1175, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1172, c_944])).
% 3.13/1.52  tff(c_1179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_946, c_1175])).
% 3.13/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.52  
% 3.13/1.52  Inference rules
% 3.13/1.52  ----------------------
% 3.13/1.52  #Ref     : 0
% 3.13/1.52  #Sup     : 227
% 3.13/1.52  #Fact    : 0
% 3.13/1.52  #Define  : 0
% 3.13/1.52  #Split   : 9
% 3.13/1.52  #Chain   : 0
% 3.13/1.52  #Close   : 0
% 3.13/1.52  
% 3.13/1.52  Ordering : KBO
% 3.13/1.52  
% 3.13/1.52  Simplification rules
% 3.13/1.52  ----------------------
% 3.13/1.52  #Subsume      : 81
% 3.13/1.52  #Demod        : 19
% 3.13/1.52  #Tautology    : 37
% 3.13/1.52  #SimpNegUnit  : 55
% 3.13/1.52  #BackRed      : 10
% 3.13/1.52  
% 3.13/1.52  #Partial instantiations: 0
% 3.13/1.52  #Strategies tried      : 1
% 3.13/1.52  
% 3.13/1.52  Timing (in seconds)
% 3.13/1.52  ----------------------
% 3.13/1.52  Preprocessing        : 0.31
% 3.13/1.52  Parsing              : 0.16
% 3.13/1.52  CNF conversion       : 0.02
% 3.13/1.52  Main loop            : 0.42
% 3.13/1.52  Inferencing          : 0.17
% 3.13/1.52  Reduction            : 0.11
% 3.13/1.52  Demodulation         : 0.06
% 3.13/1.52  BG Simplification    : 0.02
% 3.13/1.52  Subsumption          : 0.09
% 3.13/1.52  Abstraction          : 0.02
% 3.13/1.52  MUC search           : 0.00
% 3.13/1.52  Cooper               : 0.00
% 3.13/1.52  Total                : 0.77
% 3.13/1.52  Index Insertion      : 0.00
% 3.13/1.52  Index Deletion       : 0.00
% 3.13/1.52  Index Matching       : 0.00
% 3.13/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
