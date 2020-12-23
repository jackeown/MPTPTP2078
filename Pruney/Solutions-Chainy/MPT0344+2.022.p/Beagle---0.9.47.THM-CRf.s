%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:22 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 348 expanded)
%              Number of leaves         :   28 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  131 ( 787 expanded)
%              Number of equality atoms :   26 ( 177 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_60,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    ! [B_22,A_21] :
      ( m1_subset_1(B_22,A_21)
      | ~ v1_xboole_0(B_22)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_164,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,A_50)
      | ~ m1_subset_1(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,(
    ! [C_28] :
      ( ~ r2_hidden(C_28,'#skF_5')
      | ~ m1_subset_1(C_28,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_179,plain,(
    ! [B_49] :
      ( ~ m1_subset_1(B_49,'#skF_4')
      | ~ m1_subset_1(B_49,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_164,c_48])).

tff(c_212,plain,(
    ! [B_57] :
      ( ~ m1_subset_1(B_57,'#skF_4')
      | ~ m1_subset_1(B_57,'#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_217,plain,(
    ! [B_22] :
      ( ~ m1_subset_1(B_22,'#skF_4')
      | ~ v1_xboole_0(B_22)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_212])).

tff(c_218,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_77,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_1'(A_33),A_33)
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_77,c_48])).

tff(c_84,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_81])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_189,plain,(
    ! [B_53,A_54] :
      ( m1_subset_1(B_53,A_54)
      | ~ r2_hidden(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_205,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),A_2)
      | v1_xboole_0(A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(resolution,[status(thm)],[c_6,c_189])).

tff(c_85,plain,(
    ! [B_34,A_35] :
      ( m1_subset_1(B_34,A_35)
      | ~ v1_xboole_0(B_34)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_89,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_85,c_84])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( r2_hidden(B_22,A_21)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_349,plain,(
    ! [C_68,A_69,B_70] :
      ( r2_hidden(C_68,A_69)
      | ~ r2_hidden(C_68,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1171,plain,(
    ! [B_131,A_132,A_133] :
      ( r2_hidden(B_131,A_132)
      | ~ m1_subset_1(A_133,k1_zfmisc_1(A_132))
      | ~ m1_subset_1(B_131,A_133)
      | v1_xboole_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_40,c_349])).

tff(c_1185,plain,(
    ! [B_131] :
      ( r2_hidden(B_131,'#skF_4')
      | ~ m1_subset_1(B_131,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_1171])).

tff(c_1197,plain,(
    ! [B_134] :
      ( r2_hidden(B_134,'#skF_4')
      | ~ m1_subset_1(B_134,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1185])).

tff(c_38,plain,(
    ! [B_22,A_21] :
      ( m1_subset_1(B_22,A_21)
      | ~ r2_hidden(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1205,plain,(
    ! [B_134] :
      ( m1_subset_1(B_134,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_134,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1197,c_38])).

tff(c_1211,plain,(
    ! [B_135] :
      ( m1_subset_1(B_135,'#skF_4')
      | ~ m1_subset_1(B_135,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1205])).

tff(c_1215,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_205,c_1211])).

tff(c_1223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_218,c_84,c_1215])).

tff(c_1225,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1228,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1225,c_4])).

tff(c_1232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1228])).

tff(c_1234,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1238,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1234,c_4])).

tff(c_1245,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_50])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1242,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_1238,c_12])).

tff(c_30,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1241,plain,(
    k1_zfmisc_1('#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_1238,c_30])).

tff(c_1268,plain,(
    m1_subset_1('#skF_5',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_52])).

tff(c_1296,plain,(
    ! [B_144,A_145] :
      ( v1_xboole_0(B_144)
      | ~ m1_subset_1(B_144,A_145)
      | ~ v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1303,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1268,c_1296])).

tff(c_1305,plain,(
    ~ v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1303])).

tff(c_1393,plain,(
    ! [B_160,A_161] :
      ( r2_hidden(B_160,A_161)
      | ~ m1_subset_1(B_160,A_161)
      | v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1287,plain,(
    ! [C_142,A_143] :
      ( r1_tarski(C_142,A_143)
      | ~ r2_hidden(C_142,k1_zfmisc_1(A_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1294,plain,(
    ! [C_142] :
      ( r1_tarski(C_142,'#skF_4')
      | ~ r2_hidden(C_142,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_1287])).

tff(c_1400,plain,(
    ! [B_160] :
      ( r1_tarski(B_160,'#skF_4')
      | ~ m1_subset_1(B_160,k1_tarski('#skF_4'))
      | v1_xboole_0(k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1393,c_1294])).

tff(c_1415,plain,(
    ! [B_162] :
      ( r1_tarski(B_162,'#skF_4')
      | ~ m1_subset_1(B_162,k1_tarski('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1305,c_1400])).

tff(c_1427,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1268,c_1415])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1431,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1427,c_10])).

tff(c_1433,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1431])).

tff(c_1435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1245,c_1433])).

tff(c_1436,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1303])).

tff(c_1240,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_4])).

tff(c_1440,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1436,c_1240])).

tff(c_1444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1245,c_1440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.57  
% 3.57/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.58  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.57/1.58  
% 3.57/1.58  %Foreground sorts:
% 3.57/1.58  
% 3.57/1.58  
% 3.57/1.58  %Background operators:
% 3.57/1.58  
% 3.57/1.58  
% 3.57/1.58  %Foreground operators:
% 3.57/1.58  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.57/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.57/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.57/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.57/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.57/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.57/1.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.57/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.57/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.57/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.57/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.58  
% 3.57/1.59  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 3.57/1.59  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.57/1.59  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.57/1.59  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.57/1.59  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.57/1.59  tff(f_46, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.57/1.59  tff(f_60, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 3.57/1.59  tff(f_55, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.57/1.59  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.57/1.59  tff(c_50, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.57/1.59  tff(c_42, plain, (![B_22, A_21]: (m1_subset_1(B_22, A_21) | ~v1_xboole_0(B_22) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.57/1.59  tff(c_164, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | ~m1_subset_1(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.57/1.59  tff(c_48, plain, (![C_28]: (~r2_hidden(C_28, '#skF_5') | ~m1_subset_1(C_28, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.57/1.59  tff(c_179, plain, (![B_49]: (~m1_subset_1(B_49, '#skF_4') | ~m1_subset_1(B_49, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_164, c_48])).
% 3.57/1.59  tff(c_212, plain, (![B_57]: (~m1_subset_1(B_57, '#skF_4') | ~m1_subset_1(B_57, '#skF_5'))), inference(splitLeft, [status(thm)], [c_179])).
% 3.57/1.59  tff(c_217, plain, (![B_22]: (~m1_subset_1(B_22, '#skF_4') | ~v1_xboole_0(B_22) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_212])).
% 3.57/1.59  tff(c_218, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_217])).
% 3.57/1.59  tff(c_77, plain, (![A_33]: (r2_hidden('#skF_1'(A_33), A_33) | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.57/1.59  tff(c_81, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_77, c_48])).
% 3.57/1.59  tff(c_84, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_81])).
% 3.57/1.59  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.57/1.59  tff(c_189, plain, (![B_53, A_54]: (m1_subset_1(B_53, A_54) | ~r2_hidden(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.57/1.59  tff(c_205, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2) | v1_xboole_0(A_2) | k1_xboole_0=A_2)), inference(resolution, [status(thm)], [c_6, c_189])).
% 3.57/1.59  tff(c_85, plain, (![B_34, A_35]: (m1_subset_1(B_34, A_35) | ~v1_xboole_0(B_34) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.57/1.59  tff(c_89, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_85, c_84])).
% 3.57/1.59  tff(c_90, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_89])).
% 3.57/1.59  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.57/1.59  tff(c_40, plain, (![B_22, A_21]: (r2_hidden(B_22, A_21) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.57/1.59  tff(c_349, plain, (![C_68, A_69, B_70]: (r2_hidden(C_68, A_69) | ~r2_hidden(C_68, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.57/1.59  tff(c_1171, plain, (![B_131, A_132, A_133]: (r2_hidden(B_131, A_132) | ~m1_subset_1(A_133, k1_zfmisc_1(A_132)) | ~m1_subset_1(B_131, A_133) | v1_xboole_0(A_133))), inference(resolution, [status(thm)], [c_40, c_349])).
% 3.57/1.59  tff(c_1185, plain, (![B_131]: (r2_hidden(B_131, '#skF_4') | ~m1_subset_1(B_131, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_1171])).
% 3.57/1.59  tff(c_1197, plain, (![B_134]: (r2_hidden(B_134, '#skF_4') | ~m1_subset_1(B_134, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_218, c_1185])).
% 3.57/1.59  tff(c_38, plain, (![B_22, A_21]: (m1_subset_1(B_22, A_21) | ~r2_hidden(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.57/1.59  tff(c_1205, plain, (![B_134]: (m1_subset_1(B_134, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_134, '#skF_5'))), inference(resolution, [status(thm)], [c_1197, c_38])).
% 3.57/1.59  tff(c_1211, plain, (![B_135]: (m1_subset_1(B_135, '#skF_4') | ~m1_subset_1(B_135, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_90, c_1205])).
% 3.57/1.59  tff(c_1215, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_205, c_1211])).
% 3.57/1.59  tff(c_1223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_218, c_84, c_1215])).
% 3.57/1.59  tff(c_1225, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_217])).
% 3.57/1.59  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.57/1.59  tff(c_1228, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1225, c_4])).
% 3.57/1.59  tff(c_1232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1228])).
% 3.57/1.59  tff(c_1234, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_89])).
% 3.57/1.59  tff(c_1238, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1234, c_4])).
% 3.57/1.59  tff(c_1245, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_50])).
% 3.57/1.59  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.57/1.59  tff(c_1242, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_1238, c_12])).
% 3.57/1.59  tff(c_30, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.57/1.59  tff(c_1241, plain, (k1_zfmisc_1('#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_1238, c_30])).
% 3.57/1.59  tff(c_1268, plain, (m1_subset_1('#skF_5', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_52])).
% 3.57/1.59  tff(c_1296, plain, (![B_144, A_145]: (v1_xboole_0(B_144) | ~m1_subset_1(B_144, A_145) | ~v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.57/1.59  tff(c_1303, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_1268, c_1296])).
% 3.57/1.59  tff(c_1305, plain, (~v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_1303])).
% 3.57/1.59  tff(c_1393, plain, (![B_160, A_161]: (r2_hidden(B_160, A_161) | ~m1_subset_1(B_160, A_161) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.57/1.59  tff(c_1287, plain, (![C_142, A_143]: (r1_tarski(C_142, A_143) | ~r2_hidden(C_142, k1_zfmisc_1(A_143)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.57/1.59  tff(c_1294, plain, (![C_142]: (r1_tarski(C_142, '#skF_4') | ~r2_hidden(C_142, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1241, c_1287])).
% 3.57/1.59  tff(c_1400, plain, (![B_160]: (r1_tarski(B_160, '#skF_4') | ~m1_subset_1(B_160, k1_tarski('#skF_4')) | v1_xboole_0(k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_1393, c_1294])).
% 3.57/1.59  tff(c_1415, plain, (![B_162]: (r1_tarski(B_162, '#skF_4') | ~m1_subset_1(B_162, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1305, c_1400])).
% 3.57/1.59  tff(c_1427, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1268, c_1415])).
% 3.57/1.59  tff(c_10, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.57/1.59  tff(c_1431, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_1427, c_10])).
% 3.57/1.59  tff(c_1433, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1242, c_1431])).
% 3.57/1.59  tff(c_1435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1245, c_1433])).
% 3.57/1.59  tff(c_1436, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1303])).
% 3.57/1.59  tff(c_1240, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_4])).
% 3.57/1.59  tff(c_1440, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1436, c_1240])).
% 3.57/1.59  tff(c_1444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1245, c_1440])).
% 3.57/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.59  
% 3.57/1.59  Inference rules
% 3.57/1.59  ----------------------
% 3.57/1.59  #Ref     : 0
% 3.57/1.59  #Sup     : 312
% 3.57/1.59  #Fact    : 0
% 3.57/1.59  #Define  : 0
% 3.57/1.59  #Split   : 12
% 3.57/1.59  #Chain   : 0
% 3.57/1.59  #Close   : 0
% 3.57/1.59  
% 3.57/1.59  Ordering : KBO
% 3.57/1.59  
% 3.57/1.59  Simplification rules
% 3.57/1.59  ----------------------
% 3.57/1.60  #Subsume      : 40
% 3.57/1.60  #Demod        : 91
% 3.57/1.60  #Tautology    : 128
% 3.57/1.60  #SimpNegUnit  : 51
% 3.57/1.60  #BackRed      : 10
% 3.57/1.60  
% 3.57/1.60  #Partial instantiations: 0
% 3.57/1.60  #Strategies tried      : 1
% 3.57/1.60  
% 3.57/1.60  Timing (in seconds)
% 3.57/1.60  ----------------------
% 3.57/1.60  Preprocessing        : 0.31
% 3.57/1.60  Parsing              : 0.15
% 3.57/1.60  CNF conversion       : 0.02
% 3.57/1.60  Main loop            : 0.51
% 3.57/1.60  Inferencing          : 0.19
% 3.57/1.60  Reduction            : 0.16
% 3.57/1.60  Demodulation         : 0.09
% 3.57/1.60  BG Simplification    : 0.02
% 3.57/1.60  Subsumption          : 0.09
% 3.57/1.60  Abstraction          : 0.02
% 3.57/1.60  MUC search           : 0.00
% 3.57/1.60  Cooper               : 0.00
% 3.57/1.60  Total                : 0.85
% 3.57/1.60  Index Insertion      : 0.00
% 3.57/1.60  Index Deletion       : 0.00
% 3.57/1.60  Index Matching       : 0.00
% 3.57/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
