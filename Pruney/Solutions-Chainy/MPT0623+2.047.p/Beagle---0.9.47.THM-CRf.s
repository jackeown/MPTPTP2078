%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:12 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 237 expanded)
%              Number of leaves         :   32 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  157 ( 654 expanded)
%              Number of equality atoms :   87 ( 356 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_88,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_48,plain,(
    ! [A_20] : v1_relat_1('#skF_6'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ! [A_20] : v1_funct_1('#skF_6'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    ! [A_20] : k1_relat_1('#skF_6'(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_593,plain,(
    ! [A_116,B_117] :
      ( r2_hidden('#skF_2'(A_116,B_117),B_117)
      | r2_hidden('#skF_3'(A_116,B_117),A_116)
      | B_117 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_98,plain,(
    ! [A_42,B_43] : ~ r2_hidden(A_42,k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,(
    ! [A_15] : ~ r2_hidden(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_98])).

tff(c_623,plain,(
    ! [B_117] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_117),B_117)
      | k1_xboole_0 = B_117 ) ),
    inference(resolution,[status(thm)],[c_593,c_104])).

tff(c_52,plain,(
    ! [A_26,B_30] :
      ( k1_relat_1('#skF_7'(A_26,B_30)) = A_26
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_54,plain,(
    ! [A_26,B_30] :
      ( v1_funct_1('#skF_7'(A_26,B_30))
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_56,plain,(
    ! [A_26,B_30] :
      ( v1_relat_1('#skF_7'(A_26,B_30))
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_133,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_236,plain,(
    ! [A_76,B_77] :
      ( '#skF_1'(k1_tarski(A_76),B_77) = A_76
      | r1_tarski(k1_tarski(A_76),B_77) ) ),
    inference(resolution,[status(thm)],[c_133,c_18])).

tff(c_164,plain,(
    ! [A_62,B_63] :
      ( k2_relat_1('#skF_7'(A_62,B_63)) = k1_tarski(B_63)
      | k1_xboole_0 = A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_58,plain,(
    ! [C_33] :
      ( ~ r1_tarski(k2_relat_1(C_33),'#skF_8')
      | k1_relat_1(C_33) != '#skF_9'
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_170,plain,(
    ! [B_63,A_62] :
      ( ~ r1_tarski(k1_tarski(B_63),'#skF_8')
      | k1_relat_1('#skF_7'(A_62,B_63)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_62,B_63))
      | ~ v1_relat_1('#skF_7'(A_62,B_63))
      | k1_xboole_0 = A_62 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_58])).

tff(c_331,plain,(
    ! [A_91,A_92] :
      ( k1_relat_1('#skF_7'(A_91,A_92)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_91,A_92))
      | ~ v1_relat_1('#skF_7'(A_91,A_92))
      | k1_xboole_0 = A_91
      | '#skF_1'(k1_tarski(A_92),'#skF_8') = A_92 ) ),
    inference(resolution,[status(thm)],[c_236,c_170])).

tff(c_624,plain,(
    ! [A_118,B_119] :
      ( k1_relat_1('#skF_7'(A_118,B_119)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_118,B_119))
      | '#skF_1'(k1_tarski(B_119),'#skF_8') = B_119
      | k1_xboole_0 = A_118 ) ),
    inference(resolution,[status(thm)],[c_56,c_331])).

tff(c_885,plain,(
    ! [A_145,B_146] :
      ( k1_relat_1('#skF_7'(A_145,B_146)) != '#skF_9'
      | '#skF_1'(k1_tarski(B_146),'#skF_8') = B_146
      | k1_xboole_0 = A_145 ) ),
    inference(resolution,[status(thm)],[c_54,c_624])).

tff(c_888,plain,(
    ! [A_26,B_30] :
      ( A_26 != '#skF_9'
      | '#skF_1'(k1_tarski(B_30),'#skF_8') = B_30
      | k1_xboole_0 = A_26
      | k1_xboole_0 = A_26 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_885])).

tff(c_976,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_176,plain,(
    ! [A_64] :
      ( k2_relat_1(A_64) = k1_xboole_0
      | k1_relat_1(A_64) != k1_xboole_0
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_182,plain,(
    ! [A_20] :
      ( k2_relat_1('#skF_6'(A_20)) = k1_xboole_0
      | k1_relat_1('#skF_6'(A_20)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_176])).

tff(c_187,plain,(
    ! [A_65] :
      ( k2_relat_1('#skF_6'(A_65)) = k1_xboole_0
      | k1_xboole_0 != A_65 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_182])).

tff(c_193,plain,(
    ! [A_65] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_8')
      | k1_relat_1('#skF_6'(A_65)) != '#skF_9'
      | ~ v1_funct_1('#skF_6'(A_65))
      | ~ v1_relat_1('#skF_6'(A_65))
      | k1_xboole_0 != A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_58])).

tff(c_199,plain,(
    ! [A_65] :
      ( A_65 != '#skF_9'
      | k1_xboole_0 != A_65 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_16,c_193])).

tff(c_214,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_199])).

tff(c_1011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_214])).

tff(c_1014,plain,(
    ! [B_154] : '#skF_1'(k1_tarski(B_154),'#skF_8') = B_154 ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1045,plain,(
    ! [B_155] :
      ( ~ r2_hidden(B_155,'#skF_8')
      | r1_tarski(k1_tarski(B_155),'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_4])).

tff(c_1126,plain,(
    ! [A_166,B_167] :
      ( k1_relat_1('#skF_7'(A_166,B_167)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_166,B_167))
      | ~ v1_relat_1('#skF_7'(A_166,B_167))
      | k1_xboole_0 = A_166
      | ~ r2_hidden(B_167,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1045,c_170])).

tff(c_1352,plain,(
    ! [A_185,B_186] :
      ( k1_relat_1('#skF_7'(A_185,B_186)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_185,B_186))
      | ~ r2_hidden(B_186,'#skF_8')
      | k1_xboole_0 = A_185 ) ),
    inference(resolution,[status(thm)],[c_56,c_1126])).

tff(c_1357,plain,(
    ! [A_187,B_188] :
      ( k1_relat_1('#skF_7'(A_187,B_188)) != '#skF_9'
      | ~ r2_hidden(B_188,'#skF_8')
      | k1_xboole_0 = A_187 ) ),
    inference(resolution,[status(thm)],[c_54,c_1352])).

tff(c_1360,plain,(
    ! [A_26,B_30] :
      ( A_26 != '#skF_9'
      | ~ r2_hidden(B_30,'#skF_8')
      | k1_xboole_0 = A_26
      | k1_xboole_0 = A_26 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1357])).

tff(c_1364,plain,(
    ! [B_189] : ~ r2_hidden(B_189,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1360])).

tff(c_1388,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_623,c_1364])).

tff(c_1419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1388])).

tff(c_1421,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1360])).

tff(c_1460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_214])).

tff(c_1462,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1461,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1468,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1462,c_1461])).

tff(c_1463,plain,(
    ! [A_9] : r1_tarski('#skF_9',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1461,c_16])).

tff(c_1477,plain,(
    ! [A_9] : r1_tarski('#skF_8',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_1463])).

tff(c_40,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) = k1_xboole_0
      | k1_relat_1(A_19) != k1_xboole_0
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1553,plain,(
    ! [A_209] :
      ( k2_relat_1(A_209) = '#skF_8'
      | k1_relat_1(A_209) != '#skF_8'
      | ~ v1_relat_1(A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1462,c_1462,c_40])).

tff(c_1559,plain,(
    ! [A_20] :
      ( k2_relat_1('#skF_6'(A_20)) = '#skF_8'
      | k1_relat_1('#skF_6'(A_20)) != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_48,c_1553])).

tff(c_1565,plain,(
    ! [A_211] :
      ( k2_relat_1('#skF_6'(A_211)) = '#skF_8'
      | A_211 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1559])).

tff(c_1503,plain,(
    ! [C_33] :
      ( ~ r1_tarski(k2_relat_1(C_33),'#skF_8')
      | k1_relat_1(C_33) != '#skF_8'
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_58])).

tff(c_1571,plain,(
    ! [A_211] :
      ( ~ r1_tarski('#skF_8','#skF_8')
      | k1_relat_1('#skF_6'(A_211)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_211))
      | ~ v1_relat_1('#skF_6'(A_211))
      | A_211 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1565,c_1503])).

tff(c_1577,plain,(
    ! [A_211] : A_211 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1477,c_1571])).

tff(c_1487,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1462,c_1462,c_32])).

tff(c_1588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1577,c_1487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n025.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 19:21:05 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.55  
% 3.51/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.55  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 3.51/1.55  
% 3.51/1.55  %Foreground sorts:
% 3.51/1.55  
% 3.51/1.55  
% 3.51/1.55  %Background operators:
% 3.51/1.55  
% 3.51/1.55  
% 3.51/1.55  %Foreground operators:
% 3.51/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.51/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.51/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.51/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.51/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.51/1.55  tff('#skF_9', type, '#skF_9': $i).
% 3.51/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.51/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.51/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.51/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.51/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.51/1.55  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.51/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.51/1.55  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.51/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.51/1.55  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.51/1.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.51/1.55  
% 3.51/1.57  tff(f_75, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.51/1.57  tff(f_106, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 3.51/1.57  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.51/1.57  tff(f_54, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.51/1.57  tff(f_57, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.51/1.57  tff(f_88, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 3.51/1.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.51/1.57  tff(f_48, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.51/1.57  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.51/1.57  tff(f_63, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.51/1.57  tff(c_48, plain, (![A_20]: (v1_relat_1('#skF_6'(A_20)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.51/1.57  tff(c_46, plain, (![A_20]: (v1_funct_1('#skF_6'(A_20)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.51/1.57  tff(c_44, plain, (![A_20]: (k1_relat_1('#skF_6'(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.51/1.57  tff(c_60, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.51/1.57  tff(c_74, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_60])).
% 3.51/1.57  tff(c_593, plain, (![A_116, B_117]: (r2_hidden('#skF_2'(A_116, B_117), B_117) | r2_hidden('#skF_3'(A_116, B_117), A_116) | B_117=A_116)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.51/1.57  tff(c_32, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.51/1.57  tff(c_98, plain, (![A_42, B_43]: (~r2_hidden(A_42, k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.51/1.57  tff(c_104, plain, (![A_15]: (~r2_hidden(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_98])).
% 3.51/1.57  tff(c_623, plain, (![B_117]: (r2_hidden('#skF_2'(k1_xboole_0, B_117), B_117) | k1_xboole_0=B_117)), inference(resolution, [status(thm)], [c_593, c_104])).
% 3.51/1.57  tff(c_52, plain, (![A_26, B_30]: (k1_relat_1('#skF_7'(A_26, B_30))=A_26 | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.51/1.57  tff(c_54, plain, (![A_26, B_30]: (v1_funct_1('#skF_7'(A_26, B_30)) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.51/1.57  tff(c_56, plain, (![A_26, B_30]: (v1_relat_1('#skF_7'(A_26, B_30)) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.51/1.57  tff(c_133, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.51/1.57  tff(c_18, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.51/1.57  tff(c_236, plain, (![A_76, B_77]: ('#skF_1'(k1_tarski(A_76), B_77)=A_76 | r1_tarski(k1_tarski(A_76), B_77))), inference(resolution, [status(thm)], [c_133, c_18])).
% 3.51/1.57  tff(c_164, plain, (![A_62, B_63]: (k2_relat_1('#skF_7'(A_62, B_63))=k1_tarski(B_63) | k1_xboole_0=A_62)), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.51/1.57  tff(c_58, plain, (![C_33]: (~r1_tarski(k2_relat_1(C_33), '#skF_8') | k1_relat_1(C_33)!='#skF_9' | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.51/1.57  tff(c_170, plain, (![B_63, A_62]: (~r1_tarski(k1_tarski(B_63), '#skF_8') | k1_relat_1('#skF_7'(A_62, B_63))!='#skF_9' | ~v1_funct_1('#skF_7'(A_62, B_63)) | ~v1_relat_1('#skF_7'(A_62, B_63)) | k1_xboole_0=A_62)), inference(superposition, [status(thm), theory('equality')], [c_164, c_58])).
% 3.51/1.57  tff(c_331, plain, (![A_91, A_92]: (k1_relat_1('#skF_7'(A_91, A_92))!='#skF_9' | ~v1_funct_1('#skF_7'(A_91, A_92)) | ~v1_relat_1('#skF_7'(A_91, A_92)) | k1_xboole_0=A_91 | '#skF_1'(k1_tarski(A_92), '#skF_8')=A_92)), inference(resolution, [status(thm)], [c_236, c_170])).
% 3.51/1.57  tff(c_624, plain, (![A_118, B_119]: (k1_relat_1('#skF_7'(A_118, B_119))!='#skF_9' | ~v1_funct_1('#skF_7'(A_118, B_119)) | '#skF_1'(k1_tarski(B_119), '#skF_8')=B_119 | k1_xboole_0=A_118)), inference(resolution, [status(thm)], [c_56, c_331])).
% 3.51/1.57  tff(c_885, plain, (![A_145, B_146]: (k1_relat_1('#skF_7'(A_145, B_146))!='#skF_9' | '#skF_1'(k1_tarski(B_146), '#skF_8')=B_146 | k1_xboole_0=A_145)), inference(resolution, [status(thm)], [c_54, c_624])).
% 3.51/1.57  tff(c_888, plain, (![A_26, B_30]: (A_26!='#skF_9' | '#skF_1'(k1_tarski(B_30), '#skF_8')=B_30 | k1_xboole_0=A_26 | k1_xboole_0=A_26)), inference(superposition, [status(thm), theory('equality')], [c_52, c_885])).
% 3.51/1.57  tff(c_976, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_888])).
% 3.51/1.57  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.51/1.57  tff(c_176, plain, (![A_64]: (k2_relat_1(A_64)=k1_xboole_0 | k1_relat_1(A_64)!=k1_xboole_0 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.51/1.57  tff(c_182, plain, (![A_20]: (k2_relat_1('#skF_6'(A_20))=k1_xboole_0 | k1_relat_1('#skF_6'(A_20))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_176])).
% 3.51/1.57  tff(c_187, plain, (![A_65]: (k2_relat_1('#skF_6'(A_65))=k1_xboole_0 | k1_xboole_0!=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_182])).
% 3.51/1.57  tff(c_193, plain, (![A_65]: (~r1_tarski(k1_xboole_0, '#skF_8') | k1_relat_1('#skF_6'(A_65))!='#skF_9' | ~v1_funct_1('#skF_6'(A_65)) | ~v1_relat_1('#skF_6'(A_65)) | k1_xboole_0!=A_65)), inference(superposition, [status(thm), theory('equality')], [c_187, c_58])).
% 3.51/1.57  tff(c_199, plain, (![A_65]: (A_65!='#skF_9' | k1_xboole_0!=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_16, c_193])).
% 3.51/1.57  tff(c_214, plain, (k1_xboole_0!='#skF_9'), inference(reflexivity, [status(thm), theory('equality')], [c_199])).
% 3.51/1.57  tff(c_1011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_976, c_214])).
% 3.51/1.57  tff(c_1014, plain, (![B_154]: ('#skF_1'(k1_tarski(B_154), '#skF_8')=B_154)), inference(splitRight, [status(thm)], [c_888])).
% 3.51/1.57  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.51/1.57  tff(c_1045, plain, (![B_155]: (~r2_hidden(B_155, '#skF_8') | r1_tarski(k1_tarski(B_155), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1014, c_4])).
% 3.51/1.57  tff(c_1126, plain, (![A_166, B_167]: (k1_relat_1('#skF_7'(A_166, B_167))!='#skF_9' | ~v1_funct_1('#skF_7'(A_166, B_167)) | ~v1_relat_1('#skF_7'(A_166, B_167)) | k1_xboole_0=A_166 | ~r2_hidden(B_167, '#skF_8'))), inference(resolution, [status(thm)], [c_1045, c_170])).
% 3.51/1.57  tff(c_1352, plain, (![A_185, B_186]: (k1_relat_1('#skF_7'(A_185, B_186))!='#skF_9' | ~v1_funct_1('#skF_7'(A_185, B_186)) | ~r2_hidden(B_186, '#skF_8') | k1_xboole_0=A_185)), inference(resolution, [status(thm)], [c_56, c_1126])).
% 3.51/1.57  tff(c_1357, plain, (![A_187, B_188]: (k1_relat_1('#skF_7'(A_187, B_188))!='#skF_9' | ~r2_hidden(B_188, '#skF_8') | k1_xboole_0=A_187)), inference(resolution, [status(thm)], [c_54, c_1352])).
% 3.51/1.57  tff(c_1360, plain, (![A_26, B_30]: (A_26!='#skF_9' | ~r2_hidden(B_30, '#skF_8') | k1_xboole_0=A_26 | k1_xboole_0=A_26)), inference(superposition, [status(thm), theory('equality')], [c_52, c_1357])).
% 3.51/1.57  tff(c_1364, plain, (![B_189]: (~r2_hidden(B_189, '#skF_8'))), inference(splitLeft, [status(thm)], [c_1360])).
% 3.51/1.57  tff(c_1388, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_623, c_1364])).
% 3.51/1.57  tff(c_1419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1388])).
% 3.51/1.57  tff(c_1421, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1360])).
% 3.51/1.57  tff(c_1460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1421, c_214])).
% 3.51/1.57  tff(c_1462, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 3.51/1.57  tff(c_1461, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_60])).
% 3.51/1.57  tff(c_1468, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1462, c_1461])).
% 3.51/1.57  tff(c_1463, plain, (![A_9]: (r1_tarski('#skF_9', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_1461, c_16])).
% 3.51/1.57  tff(c_1477, plain, (![A_9]: (r1_tarski('#skF_8', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_1468, c_1463])).
% 3.51/1.57  tff(c_40, plain, (![A_19]: (k2_relat_1(A_19)=k1_xboole_0 | k1_relat_1(A_19)!=k1_xboole_0 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.51/1.57  tff(c_1553, plain, (![A_209]: (k2_relat_1(A_209)='#skF_8' | k1_relat_1(A_209)!='#skF_8' | ~v1_relat_1(A_209))), inference(demodulation, [status(thm), theory('equality')], [c_1462, c_1462, c_40])).
% 3.51/1.57  tff(c_1559, plain, (![A_20]: (k2_relat_1('#skF_6'(A_20))='#skF_8' | k1_relat_1('#skF_6'(A_20))!='#skF_8')), inference(resolution, [status(thm)], [c_48, c_1553])).
% 3.51/1.57  tff(c_1565, plain, (![A_211]: (k2_relat_1('#skF_6'(A_211))='#skF_8' | A_211!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1559])).
% 3.51/1.57  tff(c_1503, plain, (![C_33]: (~r1_tarski(k2_relat_1(C_33), '#skF_8') | k1_relat_1(C_33)!='#skF_8' | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(demodulation, [status(thm), theory('equality')], [c_1468, c_58])).
% 3.51/1.57  tff(c_1571, plain, (![A_211]: (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_6'(A_211))!='#skF_8' | ~v1_funct_1('#skF_6'(A_211)) | ~v1_relat_1('#skF_6'(A_211)) | A_211!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1565, c_1503])).
% 3.51/1.57  tff(c_1577, plain, (![A_211]: (A_211!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1477, c_1571])).
% 3.51/1.57  tff(c_1487, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1462, c_1462, c_32])).
% 3.51/1.57  tff(c_1588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1577, c_1487])).
% 3.51/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.57  
% 3.51/1.57  Inference rules
% 3.51/1.57  ----------------------
% 3.51/1.57  #Ref     : 1
% 3.51/1.57  #Sup     : 311
% 3.51/1.57  #Fact    : 0
% 3.51/1.57  #Define  : 0
% 3.51/1.57  #Split   : 4
% 3.51/1.57  #Chain   : 0
% 3.51/1.57  #Close   : 0
% 3.51/1.57  
% 3.51/1.57  Ordering : KBO
% 3.51/1.57  
% 3.51/1.57  Simplification rules
% 3.51/1.57  ----------------------
% 3.51/1.57  #Subsume      : 71
% 3.51/1.57  #Demod        : 203
% 3.51/1.57  #Tautology    : 167
% 3.51/1.57  #SimpNegUnit  : 49
% 3.51/1.57  #BackRed      : 82
% 3.51/1.57  
% 3.51/1.57  #Partial instantiations: 0
% 3.51/1.57  #Strategies tried      : 1
% 3.51/1.57  
% 3.51/1.57  Timing (in seconds)
% 3.51/1.57  ----------------------
% 3.51/1.57  Preprocessing        : 0.33
% 3.51/1.57  Parsing              : 0.17
% 3.51/1.57  CNF conversion       : 0.03
% 3.51/1.57  Main loop            : 0.49
% 3.66/1.57  Inferencing          : 0.18
% 3.66/1.57  Reduction            : 0.15
% 3.66/1.57  Demodulation         : 0.10
% 3.66/1.57  BG Simplification    : 0.03
% 3.66/1.57  Subsumption          : 0.10
% 3.66/1.57  Abstraction          : 0.03
% 3.66/1.57  MUC search           : 0.00
% 3.66/1.57  Cooper               : 0.00
% 3.66/1.57  Total                : 0.86
% 3.66/1.57  Index Insertion      : 0.00
% 3.66/1.57  Index Deletion       : 0.00
% 3.66/1.57  Index Matching       : 0.00
% 3.66/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
