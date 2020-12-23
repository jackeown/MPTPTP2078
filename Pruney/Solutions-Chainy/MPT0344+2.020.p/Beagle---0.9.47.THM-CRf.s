%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:22 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 201 expanded)
%              Number of leaves         :   22 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 ( 501 expanded)
%              Number of equality atoms :   21 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ v1_xboole_0(B_12)
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [B_28,A_29] :
      ( r2_hidden(B_28,A_29)
      | ~ m1_subset_1(B_28,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [C_18] :
      ( ~ r2_hidden(C_18,'#skF_5')
      | ~ m1_subset_1(C_18,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_79,plain,(
    ! [B_28] :
      ( ~ m1_subset_1(B_28,'#skF_4')
      | ~ m1_subset_1(B_28,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_71,c_30])).

tff(c_114,plain,(
    ! [B_36] :
      ( ~ m1_subset_1(B_36,'#skF_4')
      | ~ m1_subset_1(B_36,'#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_124,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,'#skF_4')
      | ~ v1_xboole_0(B_12)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_125,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_247,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_2'(A_51,B_52),B_52)
      | r2_hidden('#skF_3'(A_51,B_52),A_51)
      | B_52 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [B_33,A_34] :
      ( ~ r2_hidden(B_33,A_34)
      | k4_xboole_0(A_34,k1_tarski(B_33)) != A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_100,plain,(
    ! [B_33] : ~ r2_hidden(B_33,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_95])).

tff(c_284,plain,(
    ! [B_53] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_53),B_53)
      | k1_xboole_0 = B_53 ) ),
    inference(resolution,[status(thm)],[c_247,c_100])).

tff(c_297,plain,
    ( ~ m1_subset_1('#skF_2'(k1_xboole_0,'#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_284,c_30])).

tff(c_307,plain,(
    ~ m1_subset_1('#skF_2'(k1_xboole_0,'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_297])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ r2_hidden(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_304,plain,(
    ! [B_53] :
      ( m1_subset_1('#skF_2'(k1_xboole_0,B_53),B_53)
      | v1_xboole_0(B_53)
      | k1_xboole_0 = B_53 ) ),
    inference(resolution,[status(thm)],[c_284,c_20])).

tff(c_61,plain,(
    ! [B_26,A_27] :
      ( m1_subset_1(B_26,A_27)
      | ~ v1_xboole_0(B_26)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [C_23] :
      ( ~ r2_hidden(C_23,'#skF_5')
      | ~ m1_subset_1(C_23,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_53,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_48])).

tff(c_54,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_69,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_61,c_54])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_151,plain,(
    ! [C_39,A_40,B_41] :
      ( r2_hidden(C_39,A_40)
      | ~ r2_hidden(C_39,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_720,plain,(
    ! [B_86,A_87,A_88] :
      ( r2_hidden(B_86,A_87)
      | ~ m1_subset_1(A_88,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_86,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_22,c_151])).

tff(c_739,plain,(
    ! [B_86] :
      ( r2_hidden(B_86,'#skF_4')
      | ~ m1_subset_1(B_86,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_720])).

tff(c_749,plain,(
    ! [B_89] :
      ( r2_hidden(B_89,'#skF_4')
      | ~ m1_subset_1(B_89,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_739])).

tff(c_761,plain,(
    ! [B_89] :
      ( m1_subset_1(B_89,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_89,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_749,c_20])).

tff(c_811,plain,(
    ! [B_91] :
      ( m1_subset_1(B_91,'#skF_4')
      | ~ m1_subset_1(B_91,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_761])).

tff(c_823,plain,
    ( m1_subset_1('#skF_2'(k1_xboole_0,'#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_304,c_811])).

tff(c_841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_125,c_307,c_823])).

tff(c_843,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_995,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_2'(A_111,B_112),B_112)
      | r2_hidden('#skF_3'(A_111,B_112),A_111)
      | B_112 = A_111 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1039,plain,(
    ! [A_113,B_114] :
      ( ~ v1_xboole_0(A_113)
      | r2_hidden('#skF_2'(A_113,B_114),B_114)
      | B_114 = A_113 ) ),
    inference(resolution,[status(thm)],[c_995,c_2])).

tff(c_1065,plain,(
    ! [A_115] :
      ( ~ v1_xboole_0(A_115)
      | k1_xboole_0 = A_115 ) ),
    inference(resolution,[status(thm)],[c_1039,c_100])).

tff(c_1074,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_843,c_1065])).

tff(c_1083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1074])).

tff(c_1085,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_1086,plain,(
    ! [B_116,A_117] :
      ( r2_hidden(B_116,A_117)
      | ~ m1_subset_1(B_116,A_117)
      | v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1094,plain,(
    ! [B_116] :
      ( ~ m1_subset_1(B_116,'#skF_4')
      | ~ m1_subset_1(B_116,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1086,c_30])).

tff(c_1154,plain,(
    ! [B_126] :
      ( ~ m1_subset_1(B_126,'#skF_4')
      | ~ m1_subset_1(B_126,'#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_1094])).

tff(c_1164,plain,(
    ! [B_12] :
      ( ~ m1_subset_1(B_12,'#skF_4')
      | ~ v1_xboole_0(B_12)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_1154])).

tff(c_1165,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1164])).

tff(c_1166,plain,(
    ! [C_127,A_128,B_129] :
      ( r2_hidden(C_127,A_128)
      | ~ r2_hidden(C_127,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1173,plain,(
    ! [A_130,A_131] :
      ( r2_hidden('#skF_1'(A_130),A_131)
      | ~ m1_subset_1(A_130,k1_zfmisc_1(A_131))
      | v1_xboole_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_4,c_1166])).

tff(c_1213,plain,(
    ! [A_135,A_136] :
      ( ~ v1_xboole_0(A_135)
      | ~ m1_subset_1(A_136,k1_zfmisc_1(A_135))
      | v1_xboole_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_1173,c_2])).

tff(c_1224,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_1213])).

tff(c_1229,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_1224])).

tff(c_1231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1165,c_1229])).

tff(c_1234,plain,(
    ! [B_137] :
      ( ~ m1_subset_1(B_137,'#skF_4')
      | ~ v1_xboole_0(B_137) ) ),
    inference(splitRight,[status(thm)],[c_1164])).

tff(c_1242,plain,(
    ! [B_12] :
      ( ~ v1_xboole_0(B_12)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_1234])).

tff(c_1247,plain,(
    ! [B_12] : ~ v1_xboole_0(B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_1242])).

tff(c_1233,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1164])).

tff(c_1256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1247,c_1233])).

tff(c_1257,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1094])).

tff(c_1380,plain,(
    ! [A_155,B_156] :
      ( r2_hidden('#skF_2'(A_155,B_156),B_156)
      | r2_hidden('#skF_3'(A_155,B_156),A_155)
      | B_156 = A_155 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1424,plain,(
    ! [A_157,B_158] :
      ( ~ v1_xboole_0(A_157)
      | r2_hidden('#skF_2'(A_157,B_158),B_158)
      | B_158 = A_157 ) ),
    inference(resolution,[status(thm)],[c_1380,c_2])).

tff(c_1096,plain,(
    ! [B_118,A_119] :
      ( ~ r2_hidden(B_118,A_119)
      | k4_xboole_0(A_119,k1_tarski(B_118)) != A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1101,plain,(
    ! [B_118] : ~ r2_hidden(B_118,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1096])).

tff(c_1450,plain,(
    ! [A_159] :
      ( ~ v1_xboole_0(A_159)
      | k1_xboole_0 = A_159 ) ),
    inference(resolution,[status(thm)],[c_1424,c_1101])).

tff(c_1459,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1257,c_1450])).

tff(c_1471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:49:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.50  
% 3.09/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.50  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.09/1.50  
% 3.09/1.50  %Foreground sorts:
% 3.09/1.50  
% 3.09/1.50  
% 3.09/1.50  %Background operators:
% 3.09/1.50  
% 3.09/1.50  
% 3.09/1.50  %Foreground operators:
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.09/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.09/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.09/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.09/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.50  
% 3.09/1.52  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 3.09/1.52  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.09/1.52  tff(f_38, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.09/1.52  tff(f_40, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.09/1.52  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.09/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.09/1.52  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.09/1.52  tff(c_32, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.52  tff(c_24, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~v1_xboole_0(B_12) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.52  tff(c_71, plain, (![B_28, A_29]: (r2_hidden(B_28, A_29) | ~m1_subset_1(B_28, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.52  tff(c_30, plain, (![C_18]: (~r2_hidden(C_18, '#skF_5') | ~m1_subset_1(C_18, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.52  tff(c_79, plain, (![B_28]: (~m1_subset_1(B_28, '#skF_4') | ~m1_subset_1(B_28, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_71, c_30])).
% 3.09/1.52  tff(c_114, plain, (![B_36]: (~m1_subset_1(B_36, '#skF_4') | ~m1_subset_1(B_36, '#skF_5'))), inference(splitLeft, [status(thm)], [c_79])).
% 3.09/1.52  tff(c_124, plain, (![B_12]: (~m1_subset_1(B_12, '#skF_4') | ~v1_xboole_0(B_12) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_114])).
% 3.09/1.52  tff(c_125, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_124])).
% 3.09/1.52  tff(c_247, plain, (![A_51, B_52]: (r2_hidden('#skF_2'(A_51, B_52), B_52) | r2_hidden('#skF_3'(A_51, B_52), A_51) | B_52=A_51)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.09/1.52  tff(c_14, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.09/1.52  tff(c_95, plain, (![B_33, A_34]: (~r2_hidden(B_33, A_34) | k4_xboole_0(A_34, k1_tarski(B_33))!=A_34)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.09/1.52  tff(c_100, plain, (![B_33]: (~r2_hidden(B_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_95])).
% 3.09/1.52  tff(c_284, plain, (![B_53]: (r2_hidden('#skF_2'(k1_xboole_0, B_53), B_53) | k1_xboole_0=B_53)), inference(resolution, [status(thm)], [c_247, c_100])).
% 3.09/1.52  tff(c_297, plain, (~m1_subset_1('#skF_2'(k1_xboole_0, '#skF_5'), '#skF_4') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_284, c_30])).
% 3.09/1.52  tff(c_307, plain, (~m1_subset_1('#skF_2'(k1_xboole_0, '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_297])).
% 3.09/1.52  tff(c_20, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~r2_hidden(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.52  tff(c_304, plain, (![B_53]: (m1_subset_1('#skF_2'(k1_xboole_0, B_53), B_53) | v1_xboole_0(B_53) | k1_xboole_0=B_53)), inference(resolution, [status(thm)], [c_284, c_20])).
% 3.09/1.52  tff(c_61, plain, (![B_26, A_27]: (m1_subset_1(B_26, A_27) | ~v1_xboole_0(B_26) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.52  tff(c_48, plain, (![C_23]: (~r2_hidden(C_23, '#skF_5') | ~m1_subset_1(C_23, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.52  tff(c_53, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_48])).
% 3.09/1.52  tff(c_54, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_53])).
% 3.09/1.52  tff(c_69, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_61, c_54])).
% 3.09/1.52  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_69])).
% 3.09/1.52  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.09/1.52  tff(c_22, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.52  tff(c_151, plain, (![C_39, A_40, B_41]: (r2_hidden(C_39, A_40) | ~r2_hidden(C_39, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.52  tff(c_720, plain, (![B_86, A_87, A_88]: (r2_hidden(B_86, A_87) | ~m1_subset_1(A_88, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_86, A_88) | v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_22, c_151])).
% 3.09/1.52  tff(c_739, plain, (![B_86]: (r2_hidden(B_86, '#skF_4') | ~m1_subset_1(B_86, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_720])).
% 3.09/1.52  tff(c_749, plain, (![B_89]: (r2_hidden(B_89, '#skF_4') | ~m1_subset_1(B_89, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_125, c_739])).
% 3.09/1.52  tff(c_761, plain, (![B_89]: (m1_subset_1(B_89, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_89, '#skF_5'))), inference(resolution, [status(thm)], [c_749, c_20])).
% 3.09/1.52  tff(c_811, plain, (![B_91]: (m1_subset_1(B_91, '#skF_4') | ~m1_subset_1(B_91, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_761])).
% 3.09/1.52  tff(c_823, plain, (m1_subset_1('#skF_2'(k1_xboole_0, '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_304, c_811])).
% 3.09/1.52  tff(c_841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_125, c_307, c_823])).
% 3.09/1.52  tff(c_843, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_124])).
% 3.09/1.52  tff(c_995, plain, (![A_111, B_112]: (r2_hidden('#skF_2'(A_111, B_112), B_112) | r2_hidden('#skF_3'(A_111, B_112), A_111) | B_112=A_111)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.09/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.09/1.52  tff(c_1039, plain, (![A_113, B_114]: (~v1_xboole_0(A_113) | r2_hidden('#skF_2'(A_113, B_114), B_114) | B_114=A_113)), inference(resolution, [status(thm)], [c_995, c_2])).
% 3.09/1.52  tff(c_1065, plain, (![A_115]: (~v1_xboole_0(A_115) | k1_xboole_0=A_115)), inference(resolution, [status(thm)], [c_1039, c_100])).
% 3.09/1.52  tff(c_1074, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_843, c_1065])).
% 3.09/1.52  tff(c_1083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1074])).
% 3.09/1.52  tff(c_1085, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_69])).
% 3.09/1.52  tff(c_1086, plain, (![B_116, A_117]: (r2_hidden(B_116, A_117) | ~m1_subset_1(B_116, A_117) | v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.52  tff(c_1094, plain, (![B_116]: (~m1_subset_1(B_116, '#skF_4') | ~m1_subset_1(B_116, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_1086, c_30])).
% 3.09/1.52  tff(c_1154, plain, (![B_126]: (~m1_subset_1(B_126, '#skF_4') | ~m1_subset_1(B_126, '#skF_5'))), inference(splitLeft, [status(thm)], [c_1094])).
% 3.09/1.52  tff(c_1164, plain, (![B_12]: (~m1_subset_1(B_12, '#skF_4') | ~v1_xboole_0(B_12) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_1154])).
% 3.09/1.52  tff(c_1165, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1164])).
% 3.09/1.52  tff(c_1166, plain, (![C_127, A_128, B_129]: (r2_hidden(C_127, A_128) | ~r2_hidden(C_127, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.52  tff(c_1173, plain, (![A_130, A_131]: (r2_hidden('#skF_1'(A_130), A_131) | ~m1_subset_1(A_130, k1_zfmisc_1(A_131)) | v1_xboole_0(A_130))), inference(resolution, [status(thm)], [c_4, c_1166])).
% 3.09/1.52  tff(c_1213, plain, (![A_135, A_136]: (~v1_xboole_0(A_135) | ~m1_subset_1(A_136, k1_zfmisc_1(A_135)) | v1_xboole_0(A_136))), inference(resolution, [status(thm)], [c_1173, c_2])).
% 3.09/1.52  tff(c_1224, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_1213])).
% 3.09/1.52  tff(c_1229, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_1224])).
% 3.09/1.52  tff(c_1231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1165, c_1229])).
% 3.09/1.52  tff(c_1234, plain, (![B_137]: (~m1_subset_1(B_137, '#skF_4') | ~v1_xboole_0(B_137))), inference(splitRight, [status(thm)], [c_1164])).
% 3.09/1.52  tff(c_1242, plain, (![B_12]: (~v1_xboole_0(B_12) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_1234])).
% 3.09/1.52  tff(c_1247, plain, (![B_12]: (~v1_xboole_0(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_1242])).
% 3.09/1.52  tff(c_1233, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1164])).
% 3.09/1.52  tff(c_1256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1247, c_1233])).
% 3.09/1.52  tff(c_1257, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1094])).
% 3.09/1.52  tff(c_1380, plain, (![A_155, B_156]: (r2_hidden('#skF_2'(A_155, B_156), B_156) | r2_hidden('#skF_3'(A_155, B_156), A_155) | B_156=A_155)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.09/1.52  tff(c_1424, plain, (![A_157, B_158]: (~v1_xboole_0(A_157) | r2_hidden('#skF_2'(A_157, B_158), B_158) | B_158=A_157)), inference(resolution, [status(thm)], [c_1380, c_2])).
% 3.09/1.52  tff(c_1096, plain, (![B_118, A_119]: (~r2_hidden(B_118, A_119) | k4_xboole_0(A_119, k1_tarski(B_118))!=A_119)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.09/1.52  tff(c_1101, plain, (![B_118]: (~r2_hidden(B_118, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1096])).
% 3.09/1.52  tff(c_1450, plain, (![A_159]: (~v1_xboole_0(A_159) | k1_xboole_0=A_159)), inference(resolution, [status(thm)], [c_1424, c_1101])).
% 3.09/1.52  tff(c_1459, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1257, c_1450])).
% 3.09/1.52  tff(c_1471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1459])).
% 3.09/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.52  
% 3.09/1.52  Inference rules
% 3.09/1.52  ----------------------
% 3.09/1.52  #Ref     : 0
% 3.09/1.52  #Sup     : 287
% 3.09/1.52  #Fact    : 0
% 3.09/1.52  #Define  : 0
% 3.09/1.52  #Split   : 11
% 3.09/1.52  #Chain   : 0
% 3.09/1.52  #Close   : 0
% 3.09/1.52  
% 3.09/1.52  Ordering : KBO
% 3.09/1.52  
% 3.09/1.52  Simplification rules
% 3.09/1.52  ----------------------
% 3.09/1.52  #Subsume      : 62
% 3.09/1.52  #Demod        : 37
% 3.09/1.52  #Tautology    : 64
% 3.09/1.52  #SimpNegUnit  : 36
% 3.09/1.52  #BackRed      : 9
% 3.09/1.52  
% 3.09/1.52  #Partial instantiations: 0
% 3.09/1.52  #Strategies tried      : 1
% 3.09/1.52  
% 3.09/1.52  Timing (in seconds)
% 3.09/1.52  ----------------------
% 3.09/1.52  Preprocessing        : 0.29
% 3.09/1.52  Parsing              : 0.15
% 3.09/1.52  CNF conversion       : 0.02
% 3.09/1.52  Main loop            : 0.45
% 3.09/1.52  Inferencing          : 0.18
% 3.09/1.52  Reduction            : 0.11
% 3.09/1.52  Demodulation         : 0.07
% 3.09/1.52  BG Simplification    : 0.02
% 3.09/1.52  Subsumption          : 0.10
% 3.09/1.52  Abstraction          : 0.02
% 3.09/1.52  MUC search           : 0.00
% 3.09/1.52  Cooper               : 0.00
% 3.09/1.52  Total                : 0.78
% 3.09/1.52  Index Insertion      : 0.00
% 3.09/1.52  Index Deletion       : 0.00
% 3.09/1.52  Index Matching       : 0.00
% 3.09/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
