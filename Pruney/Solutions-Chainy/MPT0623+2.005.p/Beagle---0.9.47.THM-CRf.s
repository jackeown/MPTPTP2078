%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:06 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 254 expanded)
%              Number of leaves         :   29 (  92 expanded)
%              Depth                    :    9
%              Number of atoms          :  140 ( 568 expanded)
%              Number of equality atoms :   53 ( 277 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_1402,plain,(
    ! [A_173,B_174] :
      ( r2_hidden('#skF_1'(A_173,B_174),A_173)
      | r1_tarski(A_173,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1411,plain,(
    ! [A_173] : r1_tarski(A_173,A_173) ),
    inference(resolution,[status(thm)],[c_1402,c_4])).

tff(c_1275,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_1'(A_147,B_148),A_147)
      | r1_tarski(A_147,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_10,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ! [A_16,B_20] :
      ( k1_relat_1('#skF_3'(A_16,B_20)) = A_16
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_16,B_20] :
      ( v1_funct_1('#skF_3'(A_16,B_20))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    ! [A_16,B_20] :
      ( v1_relat_1('#skF_3'(A_16,B_20))
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_128,plain,(
    ! [A_48,B_49] :
      ( k2_relat_1('#skF_3'(A_48,B_49)) = k1_tarski(B_49)
      | k1_xboole_0 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    ! [C_23] :
      ( ~ r1_tarski(k2_relat_1(C_23),'#skF_4')
      | k1_relat_1(C_23) != '#skF_5'
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_167,plain,(
    ! [B_57,A_58] :
      ( ~ r1_tarski(k1_tarski(B_57),'#skF_4')
      | k1_relat_1('#skF_3'(A_58,B_57)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_58,B_57))
      | ~ v1_relat_1('#skF_3'(A_58,B_57))
      | k1_xboole_0 = A_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_40])).

tff(c_342,plain,(
    ! [A_79,A_80] :
      ( k1_relat_1('#skF_3'(A_79,A_80)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_79,A_80))
      | ~ v1_relat_1('#skF_3'(A_79,A_80))
      | k1_xboole_0 = A_79
      | ~ r2_hidden(A_80,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_167])).

tff(c_1132,plain,(
    ! [A_138,B_139] :
      ( k1_relat_1('#skF_3'(A_138,B_139)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_138,B_139))
      | ~ r2_hidden(B_139,'#skF_4')
      | k1_xboole_0 = A_138 ) ),
    inference(resolution,[status(thm)],[c_38,c_342])).

tff(c_1137,plain,(
    ! [A_140,B_141] :
      ( k1_relat_1('#skF_3'(A_140,B_141)) != '#skF_5'
      | ~ r2_hidden(B_141,'#skF_4')
      | k1_xboole_0 = A_140 ) ),
    inference(resolution,[status(thm)],[c_36,c_1132])).

tff(c_1140,plain,(
    ! [A_16,B_20] :
      ( A_16 != '#skF_5'
      | ~ r2_hidden(B_20,'#skF_4')
      | k1_xboole_0 = A_16
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1137])).

tff(c_1142,plain,(
    ! [B_142] : ~ r2_hidden(B_142,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1140])).

tff(c_1170,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_1142])).

tff(c_1180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1170])).

tff(c_1182,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1140])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_26] :
      ( v1_relat_1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_59,plain,(
    ! [A_25] :
      ( v1_funct_1(A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_63,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_69,plain,(
    ! [C_27] :
      ( ~ r1_tarski(k2_relat_1(C_27),'#skF_4')
      | k1_relat_1(C_27) != '#skF_5'
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_72,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_4')
    | k1_relat_1(k1_xboole_0) != '#skF_5'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_69])).

tff(c_74,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_4')
    | k1_xboole_0 != '#skF_5'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_28,c_72])).

tff(c_106,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_4')
    | k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_74])).

tff(c_107,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_1220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_107])).

tff(c_1222,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    ! [C_30,B_31] : ~ r2_hidden(C_30,k4_xboole_0(B_31,k1_tarski(C_30))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_76])).

tff(c_1226,plain,(
    ! [C_30] : ~ r2_hidden(C_30,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_79])).

tff(c_1284,plain,(
    ! [B_148] : r1_tarski('#skF_5',B_148) ),
    inference(resolution,[status(thm)],[c_1275,c_1226])).

tff(c_1221,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_1240,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1222,c_1221])).

tff(c_1294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_1240])).

tff(c_1296,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1295,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1306,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_1295])).

tff(c_1300,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_8])).

tff(c_1311,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1300])).

tff(c_1332,plain,(
    ! [A_152] :
      ( v1_relat_1(A_152)
      | ~ v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1336,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1311,c_1332])).

tff(c_1327,plain,(
    ! [A_151] :
      ( v1_funct_1(A_151)
      | ~ v1_xboole_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1331,plain,(
    v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1311,c_1327])).

tff(c_1299,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_1295,c_28])).

tff(c_1322,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1306,c_1299])).

tff(c_1298,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_1295,c_26])).

tff(c_1317,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1306,c_1298])).

tff(c_1337,plain,(
    ! [C_153] :
      ( ~ r1_tarski(k2_relat_1(C_153),'#skF_4')
      | k1_relat_1(C_153) != '#skF_4'
      | ~ v1_funct_1(C_153)
      | ~ v1_relat_1(C_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_40])).

tff(c_1340,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1317,c_1337])).

tff(c_1342,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1331,c_1322,c_1340])).

tff(c_1352,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_1342])).

tff(c_1415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1411,c_1352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.50  
% 3.27/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.50  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1
% 3.27/1.50  
% 3.27/1.50  %Foreground sorts:
% 3.27/1.50  
% 3.27/1.50  
% 3.27/1.50  %Background operators:
% 3.27/1.50  
% 3.27/1.50  
% 3.27/1.50  %Foreground operators:
% 3.27/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.27/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.27/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.50  
% 3.27/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.27/1.51  tff(f_96, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 3.27/1.51  tff(f_41, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.27/1.51  tff(f_78, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 3.27/1.51  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.27/1.51  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.27/1.51  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.27/1.51  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 3.27/1.51  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.27/1.51  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.27/1.51  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.27/1.51  tff(c_1402, plain, (![A_173, B_174]: (r2_hidden('#skF_1'(A_173, B_174), A_173) | r1_tarski(A_173, B_174))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.51  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.51  tff(c_1411, plain, (![A_173]: (r1_tarski(A_173, A_173))), inference(resolution, [status(thm)], [c_1402, c_4])).
% 3.27/1.51  tff(c_1275, plain, (![A_147, B_148]: (r2_hidden('#skF_1'(A_147, B_148), A_147) | r1_tarski(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.51  tff(c_42, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.27/1.51  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_42])).
% 3.27/1.51  tff(c_10, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.51  tff(c_34, plain, (![A_16, B_20]: (k1_relat_1('#skF_3'(A_16, B_20))=A_16 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.27/1.51  tff(c_36, plain, (![A_16, B_20]: (v1_funct_1('#skF_3'(A_16, B_20)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.27/1.51  tff(c_38, plain, (![A_16, B_20]: (v1_relat_1('#skF_3'(A_16, B_20)) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.27/1.51  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.51  tff(c_128, plain, (![A_48, B_49]: (k2_relat_1('#skF_3'(A_48, B_49))=k1_tarski(B_49) | k1_xboole_0=A_48)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.27/1.51  tff(c_40, plain, (![C_23]: (~r1_tarski(k2_relat_1(C_23), '#skF_4') | k1_relat_1(C_23)!='#skF_5' | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.27/1.51  tff(c_167, plain, (![B_57, A_58]: (~r1_tarski(k1_tarski(B_57), '#skF_4') | k1_relat_1('#skF_3'(A_58, B_57))!='#skF_5' | ~v1_funct_1('#skF_3'(A_58, B_57)) | ~v1_relat_1('#skF_3'(A_58, B_57)) | k1_xboole_0=A_58)), inference(superposition, [status(thm), theory('equality')], [c_128, c_40])).
% 3.27/1.51  tff(c_342, plain, (![A_79, A_80]: (k1_relat_1('#skF_3'(A_79, A_80))!='#skF_5' | ~v1_funct_1('#skF_3'(A_79, A_80)) | ~v1_relat_1('#skF_3'(A_79, A_80)) | k1_xboole_0=A_79 | ~r2_hidden(A_80, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_167])).
% 3.27/1.51  tff(c_1132, plain, (![A_138, B_139]: (k1_relat_1('#skF_3'(A_138, B_139))!='#skF_5' | ~v1_funct_1('#skF_3'(A_138, B_139)) | ~r2_hidden(B_139, '#skF_4') | k1_xboole_0=A_138)), inference(resolution, [status(thm)], [c_38, c_342])).
% 3.27/1.51  tff(c_1137, plain, (![A_140, B_141]: (k1_relat_1('#skF_3'(A_140, B_141))!='#skF_5' | ~r2_hidden(B_141, '#skF_4') | k1_xboole_0=A_140)), inference(resolution, [status(thm)], [c_36, c_1132])).
% 3.27/1.51  tff(c_1140, plain, (![A_16, B_20]: (A_16!='#skF_5' | ~r2_hidden(B_20, '#skF_4') | k1_xboole_0=A_16 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_34, c_1137])).
% 3.27/1.51  tff(c_1142, plain, (![B_142]: (~r2_hidden(B_142, '#skF_4'))), inference(splitLeft, [status(thm)], [c_1140])).
% 3.27/1.51  tff(c_1170, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10, c_1142])).
% 3.27/1.51  tff(c_1180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1170])).
% 3.27/1.51  tff(c_1182, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1140])).
% 3.27/1.51  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.51  tff(c_64, plain, (![A_26]: (v1_relat_1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.27/1.51  tff(c_68, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_64])).
% 3.27/1.51  tff(c_59, plain, (![A_25]: (v1_funct_1(A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.51  tff(c_63, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_59])).
% 3.27/1.51  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.27/1.51  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.27/1.51  tff(c_69, plain, (![C_27]: (~r1_tarski(k2_relat_1(C_27), '#skF_4') | k1_relat_1(C_27)!='#skF_5' | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.27/1.52  tff(c_72, plain, (~r1_tarski(k1_xboole_0, '#skF_4') | k1_relat_1(k1_xboole_0)!='#skF_5' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_69])).
% 3.27/1.52  tff(c_74, plain, (~r1_tarski(k1_xboole_0, '#skF_4') | k1_xboole_0!='#skF_5' | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_28, c_72])).
% 3.27/1.52  tff(c_106, plain, (~r1_tarski(k1_xboole_0, '#skF_4') | k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_74])).
% 3.27/1.52  tff(c_107, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_106])).
% 3.27/1.52  tff(c_1220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1182, c_107])).
% 3.27/1.52  tff(c_1222, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_106])).
% 3.27/1.52  tff(c_12, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.52  tff(c_76, plain, (![C_30, B_31]: (~r2_hidden(C_30, k4_xboole_0(B_31, k1_tarski(C_30))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.27/1.52  tff(c_79, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_76])).
% 3.27/1.52  tff(c_1226, plain, (![C_30]: (~r2_hidden(C_30, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_79])).
% 3.27/1.52  tff(c_1284, plain, (![B_148]: (r1_tarski('#skF_5', B_148))), inference(resolution, [status(thm)], [c_1275, c_1226])).
% 3.27/1.52  tff(c_1221, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_106])).
% 3.27/1.52  tff(c_1240, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1222, c_1221])).
% 3.27/1.52  tff(c_1294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1284, c_1240])).
% 3.27/1.52  tff(c_1296, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 3.27/1.52  tff(c_1295, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 3.27/1.52  tff(c_1306, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_1295])).
% 3.27/1.52  tff(c_1300, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_8])).
% 3.27/1.52  tff(c_1311, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1300])).
% 3.27/1.52  tff(c_1332, plain, (![A_152]: (v1_relat_1(A_152) | ~v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.27/1.52  tff(c_1336, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1311, c_1332])).
% 3.27/1.52  tff(c_1327, plain, (![A_151]: (v1_funct_1(A_151) | ~v1_xboole_0(A_151))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.52  tff(c_1331, plain, (v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1311, c_1327])).
% 3.27/1.52  tff(c_1299, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_1295, c_28])).
% 3.27/1.52  tff(c_1322, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1306, c_1299])).
% 3.27/1.52  tff(c_1298, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_1295, c_26])).
% 3.27/1.52  tff(c_1317, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1306, c_1298])).
% 3.27/1.52  tff(c_1337, plain, (![C_153]: (~r1_tarski(k2_relat_1(C_153), '#skF_4') | k1_relat_1(C_153)!='#skF_4' | ~v1_funct_1(C_153) | ~v1_relat_1(C_153))), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_40])).
% 3.27/1.52  tff(c_1340, plain, (~r1_tarski('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1317, c_1337])).
% 3.27/1.52  tff(c_1342, plain, (~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1331, c_1322, c_1340])).
% 3.27/1.52  tff(c_1352, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_1342])).
% 3.27/1.52  tff(c_1415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1411, c_1352])).
% 3.27/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.52  
% 3.27/1.52  Inference rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Ref     : 0
% 3.27/1.52  #Sup     : 298
% 3.27/1.52  #Fact    : 0
% 3.27/1.52  #Define  : 0
% 3.27/1.52  #Split   : 3
% 3.27/1.52  #Chain   : 0
% 3.27/1.52  #Close   : 0
% 3.27/1.52  
% 3.27/1.52  Ordering : KBO
% 3.27/1.52  
% 3.27/1.52  Simplification rules
% 3.27/1.52  ----------------------
% 3.27/1.52  #Subsume      : 83
% 3.27/1.52  #Demod        : 124
% 3.27/1.52  #Tautology    : 112
% 3.27/1.52  #SimpNegUnit  : 16
% 3.27/1.52  #BackRed      : 57
% 3.27/1.52  
% 3.27/1.52  #Partial instantiations: 0
% 3.27/1.52  #Strategies tried      : 1
% 3.27/1.52  
% 3.27/1.52  Timing (in seconds)
% 3.27/1.52  ----------------------
% 3.27/1.52  Preprocessing        : 0.31
% 3.27/1.52  Parsing              : 0.16
% 3.27/1.52  CNF conversion       : 0.02
% 3.27/1.52  Main loop            : 0.44
% 3.27/1.52  Inferencing          : 0.17
% 3.27/1.52  Reduction            : 0.12
% 3.27/1.52  Demodulation         : 0.08
% 3.27/1.52  BG Simplification    : 0.02
% 3.27/1.52  Subsumption          : 0.09
% 3.27/1.52  Abstraction          : 0.02
% 3.27/1.52  MUC search           : 0.00
% 3.27/1.52  Cooper               : 0.00
% 3.27/1.52  Total                : 0.78
% 3.27/1.52  Index Insertion      : 0.00
% 3.27/1.52  Index Deletion       : 0.00
% 3.27/1.52  Index Matching       : 0.00
% 3.27/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
