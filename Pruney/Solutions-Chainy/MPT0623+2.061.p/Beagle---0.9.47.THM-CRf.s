%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:14 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 335 expanded)
%              Number of leaves         :   32 ( 121 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 ( 807 expanded)
%              Number of equality atoms :   97 ( 453 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_75,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_623,plain,(
    ! [A_130,B_131] :
      ( r2_hidden(k4_tarski('#skF_1'(A_130,B_131),'#skF_2'(A_130,B_131)),A_130)
      | r2_hidden('#skF_3'(A_130,B_131),B_131)
      | k1_relat_1(A_130) = B_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [A_49,B_50] : ~ r2_hidden(A_49,k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_110,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_104])).

tff(c_672,plain,(
    ! [B_131] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_131),B_131)
      | k1_relat_1(k1_xboole_0) = B_131 ) ),
    inference(resolution,[status(thm)],[c_623,c_110])).

tff(c_686,plain,(
    ! [B_131] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_131),B_131)
      | k1_xboole_0 = B_131 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_672])).

tff(c_46,plain,(
    ! [A_34,B_38] :
      ( k1_relat_1('#skF_6'(A_34,B_38)) = A_34
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    ! [A_34,B_38] :
      ( v1_funct_1('#skF_6'(A_34,B_38))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    ! [A_34,B_38] :
      ( v1_relat_1('#skF_6'(A_34,B_38))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_277,plain,(
    ! [A_73,B_74] :
      ( k2_relat_1('#skF_6'(A_73,B_74)) = k1_tarski(B_74)
      | k1_xboole_0 = A_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    ! [C_41] :
      ( ~ r1_tarski(k2_relat_1(C_41),'#skF_7')
      | k1_relat_1(C_41) != '#skF_8'
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_290,plain,(
    ! [B_78,A_79] :
      ( ~ r1_tarski(k1_tarski(B_78),'#skF_7')
      | k1_relat_1('#skF_6'(A_79,B_78)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_79,B_78))
      | ~ v1_relat_1('#skF_6'(A_79,B_78))
      | k1_xboole_0 = A_79 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_52])).

tff(c_387,plain,(
    ! [A_98,A_99] :
      ( k1_relat_1('#skF_6'(A_98,A_99)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_98,A_99))
      | ~ v1_relat_1('#skF_6'(A_98,A_99))
      | k1_xboole_0 = A_98
      | ~ r2_hidden(A_99,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6,c_290])).

tff(c_536,plain,(
    ! [A_117,B_118] :
      ( k1_relat_1('#skF_6'(A_117,B_118)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_117,B_118))
      | ~ r2_hidden(B_118,'#skF_7')
      | k1_xboole_0 = A_117 ) ),
    inference(resolution,[status(thm)],[c_50,c_387])).

tff(c_849,plain,(
    ! [A_135,B_136] :
      ( k1_relat_1('#skF_6'(A_135,B_136)) != '#skF_8'
      | ~ r2_hidden(B_136,'#skF_7')
      | k1_xboole_0 = A_135 ) ),
    inference(resolution,[status(thm)],[c_48,c_536])).

tff(c_855,plain,(
    ! [A_34,B_38] :
      ( A_34 != '#skF_8'
      | ~ r2_hidden(B_38,'#skF_7')
      | k1_xboole_0 = A_34
      | k1_xboole_0 = A_34 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_849])).

tff(c_1234,plain,(
    ! [B_144] : ~ r2_hidden(B_144,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_855])).

tff(c_1238,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_686,c_1234])).

tff(c_1254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1238])).

tff(c_1256,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_855])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_83,plain,(
    ! [C_47] :
      ( ~ r1_tarski(k2_relat_1(C_47),'#skF_7')
      | k1_relat_1(C_47) != '#skF_8'
      | ~ v1_funct_1(C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_86,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_7')
    | k1_relat_1(k1_xboole_0) != '#skF_8'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_83])).

tff(c_88,plain,
    ( k1_xboole_0 != '#skF_8'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2,c_86])).

tff(c_114,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_38,plain,(
    ! [A_28] : k1_relat_1('#skF_5'(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    ! [A_28] : v1_relat_1('#skF_5'(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_115,plain,(
    ! [A_56] :
      ( k1_relat_1(A_56) != k1_xboole_0
      | k1_xboole_0 = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_121,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_5'(A_28)) != k1_xboole_0
      | '#skF_5'(A_28) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_115])).

tff(c_135,plain,(
    ! [A_58] :
      ( k1_xboole_0 != A_58
      | '#skF_5'(A_58) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_121])).

tff(c_145,plain,(
    ! [A_58] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_42])).

tff(c_151,plain,(
    ! [A_58] : k1_xboole_0 != A_58 ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_145])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_12])).

tff(c_163,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_165,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_1303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_165])).

tff(c_1305,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_1304,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_1306,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1304])).

tff(c_34,plain,(
    ! [A_27] :
      ( k1_relat_1(A_27) != k1_xboole_0
      | k1_xboole_0 = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1399,plain,(
    ! [A_160] :
      ( k1_relat_1(A_160) != '#skF_8'
      | A_160 = '#skF_8'
      | ~ v1_relat_1(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1305,c_34])).

tff(c_1408,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_5'(A_28)) != '#skF_8'
      | '#skF_5'(A_28) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_42,c_1399])).

tff(c_1417,plain,(
    ! [A_161] :
      ( A_161 != '#skF_8'
      | '#skF_5'(A_161) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1408])).

tff(c_40,plain,(
    ! [A_28] : v1_funct_1('#skF_5'(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1425,plain,(
    ! [A_161] :
      ( v1_funct_1('#skF_8')
      | A_161 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_40])).

tff(c_1433,plain,(
    ! [A_161] : A_161 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1306,c_1425])).

tff(c_1311,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_8',B_5) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1305,c_12])).

tff(c_1447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1433,c_1311])).

tff(c_1448,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1452,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1448,c_30])).

tff(c_1451,plain,(
    ! [A_1] : r1_tarski('#skF_8',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_2])).

tff(c_1450,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1448,c_28])).

tff(c_1449,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1457,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1449])).

tff(c_1496,plain,(
    ! [C_165] :
      ( ~ r1_tarski(k2_relat_1(C_165),'#skF_8')
      | k1_relat_1(C_165) != '#skF_8'
      | ~ v1_funct_1(C_165)
      | ~ v1_relat_1(C_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1457,c_52])).

tff(c_1499,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1450,c_1496])).

tff(c_1501,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_1451,c_1499])).

tff(c_1502,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1501])).

tff(c_1527,plain,(
    ! [A_175] :
      ( k1_relat_1(A_175) != '#skF_8'
      | A_175 = '#skF_8'
      | ~ v1_relat_1(A_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1448,c_34])).

tff(c_1533,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_5'(A_28)) != '#skF_8'
      | '#skF_5'(A_28) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_42,c_1527])).

tff(c_1539,plain,(
    ! [A_178] :
      ( A_178 != '#skF_8'
      | '#skF_5'(A_178) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1533])).

tff(c_1549,plain,(
    ! [A_178] :
      ( v1_relat_1('#skF_8')
      | A_178 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1539,c_42])).

tff(c_1555,plain,(
    ! [A_178] : A_178 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1502,c_1549])).

tff(c_1479,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1448,c_10])).

tff(c_1568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1555,c_1479])).

tff(c_1569,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1501])).

tff(c_1618,plain,(
    ! [A_193] :
      ( k1_relat_1(A_193) != '#skF_8'
      | A_193 = '#skF_8'
      | ~ v1_relat_1(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1448,c_34])).

tff(c_1627,plain,(
    ! [A_28] :
      ( k1_relat_1('#skF_5'(A_28)) != '#skF_8'
      | '#skF_5'(A_28) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_42,c_1618])).

tff(c_1636,plain,(
    ! [A_194] :
      ( A_194 != '#skF_8'
      | '#skF_5'(A_194) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1627])).

tff(c_1644,plain,(
    ! [A_194] :
      ( v1_funct_1('#skF_8')
      | A_194 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1636,c_40])).

tff(c_1652,plain,(
    ! [A_194] : A_194 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1569,c_1644])).

tff(c_1680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1652,c_1479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:13:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.46  
% 3.22/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.46  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1
% 3.22/1.46  
% 3.22/1.46  %Foreground sorts:
% 3.22/1.46  
% 3.22/1.46  
% 3.22/1.46  %Background operators:
% 3.22/1.46  
% 3.22/1.46  
% 3.22/1.46  %Foreground operators:
% 3.22/1.46  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.22/1.46  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.22/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.22/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.22/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.22/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.22/1.46  tff('#skF_8', type, '#skF_8': $i).
% 3.22/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.22/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.46  
% 3.22/1.48  tff(f_102, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 3.22/1.48  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.22/1.48  tff(f_48, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.22/1.48  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.22/1.48  tff(f_40, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.22/1.48  tff(f_84, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 3.22/1.48  tff(f_31, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.22/1.48  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.22/1.48  tff(f_71, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.22/1.48  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.22/1.48  tff(c_54, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.22/1.48  tff(c_75, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_54])).
% 3.22/1.48  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.22/1.48  tff(c_623, plain, (![A_130, B_131]: (r2_hidden(k4_tarski('#skF_1'(A_130, B_131), '#skF_2'(A_130, B_131)), A_130) | r2_hidden('#skF_3'(A_130, B_131), B_131) | k1_relat_1(A_130)=B_131)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.48  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.48  tff(c_104, plain, (![A_49, B_50]: (~r2_hidden(A_49, k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.22/1.48  tff(c_110, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_104])).
% 3.22/1.48  tff(c_672, plain, (![B_131]: (r2_hidden('#skF_3'(k1_xboole_0, B_131), B_131) | k1_relat_1(k1_xboole_0)=B_131)), inference(resolution, [status(thm)], [c_623, c_110])).
% 3.22/1.48  tff(c_686, plain, (![B_131]: (r2_hidden('#skF_3'(k1_xboole_0, B_131), B_131) | k1_xboole_0=B_131)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_672])).
% 3.22/1.48  tff(c_46, plain, (![A_34, B_38]: (k1_relat_1('#skF_6'(A_34, B_38))=A_34 | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.48  tff(c_48, plain, (![A_34, B_38]: (v1_funct_1('#skF_6'(A_34, B_38)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.48  tff(c_50, plain, (![A_34, B_38]: (v1_relat_1('#skF_6'(A_34, B_38)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.48  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.48  tff(c_277, plain, (![A_73, B_74]: (k2_relat_1('#skF_6'(A_73, B_74))=k1_tarski(B_74) | k1_xboole_0=A_73)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.22/1.48  tff(c_52, plain, (![C_41]: (~r1_tarski(k2_relat_1(C_41), '#skF_7') | k1_relat_1(C_41)!='#skF_8' | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.22/1.48  tff(c_290, plain, (![B_78, A_79]: (~r1_tarski(k1_tarski(B_78), '#skF_7') | k1_relat_1('#skF_6'(A_79, B_78))!='#skF_8' | ~v1_funct_1('#skF_6'(A_79, B_78)) | ~v1_relat_1('#skF_6'(A_79, B_78)) | k1_xboole_0=A_79)), inference(superposition, [status(thm), theory('equality')], [c_277, c_52])).
% 3.22/1.48  tff(c_387, plain, (![A_98, A_99]: (k1_relat_1('#skF_6'(A_98, A_99))!='#skF_8' | ~v1_funct_1('#skF_6'(A_98, A_99)) | ~v1_relat_1('#skF_6'(A_98, A_99)) | k1_xboole_0=A_98 | ~r2_hidden(A_99, '#skF_7'))), inference(resolution, [status(thm)], [c_6, c_290])).
% 3.22/1.48  tff(c_536, plain, (![A_117, B_118]: (k1_relat_1('#skF_6'(A_117, B_118))!='#skF_8' | ~v1_funct_1('#skF_6'(A_117, B_118)) | ~r2_hidden(B_118, '#skF_7') | k1_xboole_0=A_117)), inference(resolution, [status(thm)], [c_50, c_387])).
% 3.22/1.48  tff(c_849, plain, (![A_135, B_136]: (k1_relat_1('#skF_6'(A_135, B_136))!='#skF_8' | ~r2_hidden(B_136, '#skF_7') | k1_xboole_0=A_135)), inference(resolution, [status(thm)], [c_48, c_536])).
% 3.22/1.48  tff(c_855, plain, (![A_34, B_38]: (A_34!='#skF_8' | ~r2_hidden(B_38, '#skF_7') | k1_xboole_0=A_34 | k1_xboole_0=A_34)), inference(superposition, [status(thm), theory('equality')], [c_46, c_849])).
% 3.22/1.48  tff(c_1234, plain, (![B_144]: (~r2_hidden(B_144, '#skF_7'))), inference(splitLeft, [status(thm)], [c_855])).
% 3.22/1.48  tff(c_1238, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_686, c_1234])).
% 3.22/1.48  tff(c_1254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_1238])).
% 3.22/1.48  tff(c_1256, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_855])).
% 3.22/1.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.48  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.22/1.48  tff(c_83, plain, (![C_47]: (~r1_tarski(k2_relat_1(C_47), '#skF_7') | k1_relat_1(C_47)!='#skF_8' | ~v1_funct_1(C_47) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.22/1.48  tff(c_86, plain, (~r1_tarski(k1_xboole_0, '#skF_7') | k1_relat_1(k1_xboole_0)!='#skF_8' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_83])).
% 3.22/1.48  tff(c_88, plain, (k1_xboole_0!='#skF_8' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2, c_86])).
% 3.22/1.48  tff(c_114, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_88])).
% 3.22/1.48  tff(c_38, plain, (![A_28]: (k1_relat_1('#skF_5'(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.48  tff(c_42, plain, (![A_28]: (v1_relat_1('#skF_5'(A_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.48  tff(c_115, plain, (![A_56]: (k1_relat_1(A_56)!=k1_xboole_0 | k1_xboole_0=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.48  tff(c_121, plain, (![A_28]: (k1_relat_1('#skF_5'(A_28))!=k1_xboole_0 | '#skF_5'(A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_115])).
% 3.22/1.48  tff(c_135, plain, (![A_58]: (k1_xboole_0!=A_58 | '#skF_5'(A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_121])).
% 3.22/1.48  tff(c_145, plain, (![A_58]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_58)), inference(superposition, [status(thm), theory('equality')], [c_135, c_42])).
% 3.22/1.48  tff(c_151, plain, (![A_58]: (k1_xboole_0!=A_58)), inference(negUnitSimplification, [status(thm)], [c_114, c_145])).
% 3.22/1.48  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.22/1.48  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_12])).
% 3.22/1.48  tff(c_163, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_88])).
% 3.22/1.48  tff(c_165, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_163])).
% 3.22/1.48  tff(c_1303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1256, c_165])).
% 3.22/1.48  tff(c_1305, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_163])).
% 3.22/1.48  tff(c_1304, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_163])).
% 3.22/1.48  tff(c_1306, plain, (~v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1304])).
% 3.22/1.48  tff(c_34, plain, (![A_27]: (k1_relat_1(A_27)!=k1_xboole_0 | k1_xboole_0=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.48  tff(c_1399, plain, (![A_160]: (k1_relat_1(A_160)!='#skF_8' | A_160='#skF_8' | ~v1_relat_1(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1305, c_34])).
% 3.22/1.48  tff(c_1408, plain, (![A_28]: (k1_relat_1('#skF_5'(A_28))!='#skF_8' | '#skF_5'(A_28)='#skF_8')), inference(resolution, [status(thm)], [c_42, c_1399])).
% 3.22/1.48  tff(c_1417, plain, (![A_161]: (A_161!='#skF_8' | '#skF_5'(A_161)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1408])).
% 3.22/1.48  tff(c_40, plain, (![A_28]: (v1_funct_1('#skF_5'(A_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.48  tff(c_1425, plain, (![A_161]: (v1_funct_1('#skF_8') | A_161!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1417, c_40])).
% 3.22/1.48  tff(c_1433, plain, (![A_161]: (A_161!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1306, c_1425])).
% 3.22/1.48  tff(c_1311, plain, (![B_5]: (k2_zfmisc_1('#skF_8', B_5)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1305, c_12])).
% 3.22/1.48  tff(c_1447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1433, c_1311])).
% 3.22/1.48  tff(c_1448, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_54])).
% 3.22/1.48  tff(c_1452, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1448, c_30])).
% 3.22/1.48  tff(c_1451, plain, (![A_1]: (r1_tarski('#skF_8', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_2])).
% 3.22/1.48  tff(c_1450, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1448, c_28])).
% 3.22/1.48  tff(c_1449, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_54])).
% 3.22/1.48  tff(c_1457, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1449])).
% 3.22/1.48  tff(c_1496, plain, (![C_165]: (~r1_tarski(k2_relat_1(C_165), '#skF_8') | k1_relat_1(C_165)!='#skF_8' | ~v1_funct_1(C_165) | ~v1_relat_1(C_165))), inference(demodulation, [status(thm), theory('equality')], [c_1457, c_52])).
% 3.22/1.48  tff(c_1499, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1450, c_1496])).
% 3.22/1.48  tff(c_1501, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_1451, c_1499])).
% 3.22/1.48  tff(c_1502, plain, (~v1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1501])).
% 3.22/1.48  tff(c_1527, plain, (![A_175]: (k1_relat_1(A_175)!='#skF_8' | A_175='#skF_8' | ~v1_relat_1(A_175))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1448, c_34])).
% 3.22/1.48  tff(c_1533, plain, (![A_28]: (k1_relat_1('#skF_5'(A_28))!='#skF_8' | '#skF_5'(A_28)='#skF_8')), inference(resolution, [status(thm)], [c_42, c_1527])).
% 3.22/1.48  tff(c_1539, plain, (![A_178]: (A_178!='#skF_8' | '#skF_5'(A_178)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1533])).
% 3.22/1.48  tff(c_1549, plain, (![A_178]: (v1_relat_1('#skF_8') | A_178!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1539, c_42])).
% 3.22/1.48  tff(c_1555, plain, (![A_178]: (A_178!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1502, c_1549])).
% 3.22/1.48  tff(c_1479, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1448, c_10])).
% 3.22/1.48  tff(c_1568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1555, c_1479])).
% 3.22/1.48  tff(c_1569, plain, (~v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_1501])).
% 3.22/1.48  tff(c_1618, plain, (![A_193]: (k1_relat_1(A_193)!='#skF_8' | A_193='#skF_8' | ~v1_relat_1(A_193))), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1448, c_34])).
% 3.22/1.48  tff(c_1627, plain, (![A_28]: (k1_relat_1('#skF_5'(A_28))!='#skF_8' | '#skF_5'(A_28)='#skF_8')), inference(resolution, [status(thm)], [c_42, c_1618])).
% 3.22/1.48  tff(c_1636, plain, (![A_194]: (A_194!='#skF_8' | '#skF_5'(A_194)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1627])).
% 3.22/1.48  tff(c_1644, plain, (![A_194]: (v1_funct_1('#skF_8') | A_194!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1636, c_40])).
% 3.22/1.48  tff(c_1652, plain, (![A_194]: (A_194!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1569, c_1644])).
% 3.22/1.48  tff(c_1680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1652, c_1479])).
% 3.22/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  Inference rules
% 3.22/1.48  ----------------------
% 3.22/1.48  #Ref     : 0
% 3.22/1.48  #Sup     : 354
% 3.22/1.48  #Fact    : 0
% 3.22/1.48  #Define  : 0
% 3.22/1.48  #Split   : 6
% 3.22/1.48  #Chain   : 0
% 3.22/1.48  #Close   : 0
% 3.22/1.48  
% 3.22/1.48  Ordering : KBO
% 3.22/1.48  
% 3.22/1.48  Simplification rules
% 3.22/1.48  ----------------------
% 3.22/1.48  #Subsume      : 154
% 3.22/1.48  #Demod        : 228
% 3.22/1.48  #Tautology    : 120
% 3.22/1.48  #SimpNegUnit  : 61
% 3.22/1.48  #BackRed      : 98
% 3.22/1.48  
% 3.22/1.48  #Partial instantiations: 0
% 3.22/1.48  #Strategies tried      : 1
% 3.22/1.48  
% 3.22/1.48  Timing (in seconds)
% 3.22/1.48  ----------------------
% 3.22/1.48  Preprocessing        : 0.30
% 3.22/1.48  Parsing              : 0.16
% 3.22/1.48  CNF conversion       : 0.02
% 3.22/1.48  Main loop            : 0.43
% 3.22/1.48  Inferencing          : 0.15
% 3.22/1.48  Reduction            : 0.13
% 3.22/1.48  Demodulation         : 0.09
% 3.22/1.48  BG Simplification    : 0.02
% 3.22/1.48  Subsumption          : 0.09
% 3.22/1.48  Abstraction          : 0.02
% 3.22/1.48  MUC search           : 0.00
% 3.22/1.48  Cooper               : 0.00
% 3.22/1.48  Total                : 0.77
% 3.22/1.48  Index Insertion      : 0.00
% 3.22/1.48  Index Deletion       : 0.00
% 3.22/1.49  Index Matching       : 0.00
% 3.22/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
