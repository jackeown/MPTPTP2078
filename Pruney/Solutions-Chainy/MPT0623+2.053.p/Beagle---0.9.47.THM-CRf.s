%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:13 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 487 expanded)
%              Number of leaves         :   34 ( 166 expanded)
%              Depth                    :   15
%              Number of atoms          :  216 (1248 expanded)
%              Number of equality atoms :  121 ( 723 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

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

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_93,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_85,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_500,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_2'(A_101,B_102),B_102)
      | r2_hidden('#skF_3'(A_101,B_102),A_101)
      | B_102 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_115,plain,(
    ! [A_42,B_43] : ~ r2_hidden(A_42,k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_121,plain,(
    ! [A_15] : ~ r2_hidden(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_115])).

tff(c_531,plain,(
    ! [B_102] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_102),B_102)
      | k1_xboole_0 = B_102 ) ),
    inference(resolution,[status(thm)],[c_500,c_121])).

tff(c_56,plain,(
    ! [A_26,B_30] :
      ( k1_relat_1('#skF_7'(A_26,B_30)) = A_26
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    ! [A_26,B_30] :
      ( v1_funct_1('#skF_7'(A_26,B_30))
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60,plain,(
    ! [A_26,B_30] :
      ( v1_relat_1('#skF_7'(A_26,B_30))
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_266,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_280,plain,(
    ! [A_10,B_64] :
      ( '#skF_1'(k1_tarski(A_10),B_64) = A_10
      | r1_tarski(k1_tarski(A_10),B_64) ) ),
    inference(resolution,[status(thm)],[c_266,c_18])).

tff(c_297,plain,(
    ! [A_68,B_69] :
      ( k2_relat_1('#skF_7'(A_68,B_69)) = k1_tarski(B_69)
      | k1_xboole_0 = A_68 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    ! [C_33] :
      ( ~ r1_tarski(k2_relat_1(C_33),'#skF_8')
      | k1_relat_1(C_33) != '#skF_9'
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_379,plain,(
    ! [B_88,A_89] :
      ( ~ r1_tarski(k1_tarski(B_88),'#skF_8')
      | k1_relat_1('#skF_7'(A_89,B_88)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_89,B_88))
      | ~ v1_relat_1('#skF_7'(A_89,B_88))
      | k1_xboole_0 = A_89 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_62])).

tff(c_584,plain,(
    ! [A_105,A_106] :
      ( k1_relat_1('#skF_7'(A_105,A_106)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_105,A_106))
      | ~ v1_relat_1('#skF_7'(A_105,A_106))
      | k1_xboole_0 = A_105
      | '#skF_1'(k1_tarski(A_106),'#skF_8') = A_106 ) ),
    inference(resolution,[status(thm)],[c_280,c_379])).

tff(c_923,plain,(
    ! [A_140,B_141] :
      ( k1_relat_1('#skF_7'(A_140,B_141)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_140,B_141))
      | '#skF_1'(k1_tarski(B_141),'#skF_8') = B_141
      | k1_xboole_0 = A_140 ) ),
    inference(resolution,[status(thm)],[c_60,c_584])).

tff(c_965,plain,(
    ! [A_145,B_146] :
      ( k1_relat_1('#skF_7'(A_145,B_146)) != '#skF_9'
      | '#skF_1'(k1_tarski(B_146),'#skF_8') = B_146
      | k1_xboole_0 = A_145 ) ),
    inference(resolution,[status(thm)],[c_58,c_923])).

tff(c_968,plain,(
    ! [A_26,B_30] :
      ( A_26 != '#skF_9'
      | '#skF_1'(k1_tarski(B_30),'#skF_8') = B_30
      | k1_xboole_0 = A_26
      | k1_xboole_0 = A_26 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_965])).

tff(c_971,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_968])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_87,plain,(
    ! [C_39] :
      ( ~ r1_tarski(k2_relat_1(C_39),'#skF_8')
      | k1_relat_1(C_39) != '#skF_9'
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_90,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_8')
    | k1_relat_1(k1_xboole_0) != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_87])).

tff(c_92,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16,c_90])).

tff(c_131,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_48,plain,(
    ! [A_20] : k1_relat_1('#skF_6'(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    ! [A_20] : v1_relat_1('#skF_6'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_142,plain,(
    ! [A_53] :
      ( k1_relat_1(A_53) != k1_xboole_0
      | k1_xboole_0 = A_53
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_148,plain,(
    ! [A_20] :
      ( k1_relat_1('#skF_6'(A_20)) != k1_xboole_0
      | '#skF_6'(A_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_142])).

tff(c_153,plain,(
    ! [A_54] :
      ( k1_xboole_0 != A_54
      | '#skF_6'(A_54) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_148])).

tff(c_163,plain,(
    ! [A_54] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_54 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_52])).

tff(c_169,plain,(
    ! [A_54] : k1_xboole_0 != A_54 ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_163])).

tff(c_34,plain,(
    ! [B_16] : k2_zfmisc_1(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_34])).

tff(c_181,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_193,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_1011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_193])).

tff(c_1014,plain,(
    ! [B_147] : '#skF_1'(k1_tarski(B_147),'#skF_8') = B_147 ),
    inference(splitRight,[status(thm)],[c_968])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1048,plain,(
    ! [B_148] :
      ( ~ r2_hidden(B_148,'#skF_8')
      | r1_tarski(k1_tarski(B_148),'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_4])).

tff(c_303,plain,(
    ! [B_69,A_68] :
      ( ~ r1_tarski(k1_tarski(B_69),'#skF_8')
      | k1_relat_1('#skF_7'(A_68,B_69)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_68,B_69))
      | ~ v1_relat_1('#skF_7'(A_68,B_69))
      | k1_xboole_0 = A_68 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_62])).

tff(c_1178,plain,(
    ! [A_158,B_159] :
      ( k1_relat_1('#skF_7'(A_158,B_159)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_158,B_159))
      | ~ v1_relat_1('#skF_7'(A_158,B_159))
      | k1_xboole_0 = A_158
      | ~ r2_hidden(B_159,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1048,c_303])).

tff(c_1448,plain,(
    ! [A_183,B_184] :
      ( k1_relat_1('#skF_7'(A_183,B_184)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_183,B_184))
      | ~ r2_hidden(B_184,'#skF_8')
      | k1_xboole_0 = A_183 ) ),
    inference(resolution,[status(thm)],[c_60,c_1178])).

tff(c_1453,plain,(
    ! [A_185,B_186] :
      ( k1_relat_1('#skF_7'(A_185,B_186)) != '#skF_9'
      | ~ r2_hidden(B_186,'#skF_8')
      | k1_xboole_0 = A_185 ) ),
    inference(resolution,[status(thm)],[c_58,c_1448])).

tff(c_1456,plain,(
    ! [A_26,B_30] :
      ( A_26 != '#skF_9'
      | ~ r2_hidden(B_30,'#skF_8')
      | k1_xboole_0 = A_26
      | k1_xboole_0 = A_26 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1453])).

tff(c_1458,plain,(
    ! [B_187] : ~ r2_hidden(B_187,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1456])).

tff(c_1486,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_531,c_1458])).

tff(c_1510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1486])).

tff(c_1512,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1456])).

tff(c_1558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1512,c_193])).

tff(c_1560,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_1559,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_1579,plain,(
    ~ v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_1559])).

tff(c_1561,plain,(
    ! [A_188] :
      ( k1_relat_1(A_188) != k1_xboole_0
      | k1_xboole_0 = A_188
      | ~ v1_relat_1(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1570,plain,(
    ! [A_20] :
      ( k1_relat_1('#skF_6'(A_20)) != k1_xboole_0
      | '#skF_6'(A_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_1561])).

tff(c_1577,plain,(
    ! [A_20] :
      ( k1_xboole_0 != A_20
      | '#skF_6'(A_20) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1570])).

tff(c_1653,plain,(
    ! [A_194] :
      ( A_194 != '#skF_9'
      | '#skF_6'(A_194) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_1560,c_1577])).

tff(c_50,plain,(
    ! [A_20] : v1_funct_1('#skF_6'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1661,plain,(
    ! [A_194] :
      ( v1_funct_1('#skF_9')
      | A_194 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1653,c_50])).

tff(c_1669,plain,(
    ! [A_194] : A_194 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_1579,c_1661])).

tff(c_1586,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_1560,c_32])).

tff(c_1679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1669,c_1586])).

tff(c_1681,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1680,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1695,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_1680])).

tff(c_1690,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1680,c_1680,c_40])).

tff(c_1712,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1695,c_1690])).

tff(c_1689,plain,(
    ! [A_9] : r1_tarski('#skF_9',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1680,c_16])).

tff(c_1710,plain,(
    ! [A_9] : r1_tarski('#skF_8',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1689])).

tff(c_1688,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1680,c_1680,c_38])).

tff(c_1705,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_1695,c_1688])).

tff(c_1742,plain,(
    ! [C_200] :
      ( ~ r1_tarski(k2_relat_1(C_200),'#skF_8')
      | k1_relat_1(C_200) != '#skF_8'
      | ~ v1_funct_1(C_200)
      | ~ v1_relat_1(C_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1695,c_62])).

tff(c_1745,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1705,c_1742])).

tff(c_1747,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1712,c_1710,c_1745])).

tff(c_1748,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1747])).

tff(c_44,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1781,plain,(
    ! [A_212] :
      ( k1_relat_1(A_212) != '#skF_8'
      | A_212 = '#skF_8'
      | ~ v1_relat_1(A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_1681,c_44])).

tff(c_1787,plain,(
    ! [A_20] :
      ( k1_relat_1('#skF_6'(A_20)) != '#skF_8'
      | '#skF_6'(A_20) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_52,c_1781])).

tff(c_1792,plain,(
    ! [A_213] :
      ( A_213 != '#skF_8'
      | '#skF_6'(A_213) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1787])).

tff(c_1802,plain,(
    ! [A_213] :
      ( v1_relat_1('#skF_8')
      | A_213 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1792,c_52])).

tff(c_1808,plain,(
    ! [A_213] : A_213 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1748,c_1802])).

tff(c_1726,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_1681,c_32])).

tff(c_1821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1808,c_1726])).

tff(c_1822,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1747])).

tff(c_1856,plain,(
    ! [A_225] :
      ( k1_relat_1(A_225) != '#skF_8'
      | A_225 = '#skF_8'
      | ~ v1_relat_1(A_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_1681,c_44])).

tff(c_1865,plain,(
    ! [A_20] :
      ( k1_relat_1('#skF_6'(A_20)) != '#skF_8'
      | '#skF_6'(A_20) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_52,c_1856])).

tff(c_1874,plain,(
    ! [A_226] :
      ( A_226 != '#skF_8'
      | '#skF_6'(A_226) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1865])).

tff(c_1882,plain,(
    ! [A_226] :
      ( v1_funct_1('#skF_8')
      | A_226 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1874,c_50])).

tff(c_1890,plain,(
    ! [A_226] : A_226 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1822,c_1882])).

tff(c_1922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1890,c_1726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.65  
% 3.69/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.65  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 3.69/1.65  
% 3.69/1.65  %Foreground sorts:
% 3.69/1.65  
% 3.69/1.65  
% 3.69/1.65  %Background operators:
% 3.69/1.65  
% 3.69/1.65  
% 3.69/1.65  %Foreground operators:
% 3.69/1.65  tff(np__1, type, np__1: $i).
% 3.69/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.69/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.69/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.69/1.65  tff('#skF_9', type, '#skF_9': $i).
% 3.69/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.69/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.69/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.69/1.65  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.69/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.69/1.65  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.69/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.69/1.65  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.69/1.65  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.69/1.65  
% 3.69/1.67  tff(f_111, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 3.69/1.67  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.69/1.67  tff(f_54, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.69/1.67  tff(f_57, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.69/1.67  tff(f_93, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 3.69/1.67  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.69/1.67  tff(f_48, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.69/1.67  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.69/1.67  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.69/1.67  tff(f_80, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 3.69/1.67  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.69/1.67  tff(c_64, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.67  tff(c_85, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_64])).
% 3.69/1.67  tff(c_500, plain, (![A_101, B_102]: (r2_hidden('#skF_2'(A_101, B_102), B_102) | r2_hidden('#skF_3'(A_101, B_102), A_101) | B_102=A_101)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.69/1.67  tff(c_32, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.69/1.67  tff(c_115, plain, (![A_42, B_43]: (~r2_hidden(A_42, k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.69/1.67  tff(c_121, plain, (![A_15]: (~r2_hidden(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_115])).
% 3.69/1.67  tff(c_531, plain, (![B_102]: (r2_hidden('#skF_2'(k1_xboole_0, B_102), B_102) | k1_xboole_0=B_102)), inference(resolution, [status(thm)], [c_500, c_121])).
% 3.69/1.67  tff(c_56, plain, (![A_26, B_30]: (k1_relat_1('#skF_7'(A_26, B_30))=A_26 | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.69/1.67  tff(c_58, plain, (![A_26, B_30]: (v1_funct_1('#skF_7'(A_26, B_30)) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.69/1.67  tff(c_60, plain, (![A_26, B_30]: (v1_relat_1('#skF_7'(A_26, B_30)) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.69/1.67  tff(c_266, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.67  tff(c_18, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.69/1.67  tff(c_280, plain, (![A_10, B_64]: ('#skF_1'(k1_tarski(A_10), B_64)=A_10 | r1_tarski(k1_tarski(A_10), B_64))), inference(resolution, [status(thm)], [c_266, c_18])).
% 3.69/1.67  tff(c_297, plain, (![A_68, B_69]: (k2_relat_1('#skF_7'(A_68, B_69))=k1_tarski(B_69) | k1_xboole_0=A_68)), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.69/1.67  tff(c_62, plain, (![C_33]: (~r1_tarski(k2_relat_1(C_33), '#skF_8') | k1_relat_1(C_33)!='#skF_9' | ~v1_funct_1(C_33) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.67  tff(c_379, plain, (![B_88, A_89]: (~r1_tarski(k1_tarski(B_88), '#skF_8') | k1_relat_1('#skF_7'(A_89, B_88))!='#skF_9' | ~v1_funct_1('#skF_7'(A_89, B_88)) | ~v1_relat_1('#skF_7'(A_89, B_88)) | k1_xboole_0=A_89)), inference(superposition, [status(thm), theory('equality')], [c_297, c_62])).
% 3.69/1.67  tff(c_584, plain, (![A_105, A_106]: (k1_relat_1('#skF_7'(A_105, A_106))!='#skF_9' | ~v1_funct_1('#skF_7'(A_105, A_106)) | ~v1_relat_1('#skF_7'(A_105, A_106)) | k1_xboole_0=A_105 | '#skF_1'(k1_tarski(A_106), '#skF_8')=A_106)), inference(resolution, [status(thm)], [c_280, c_379])).
% 3.69/1.67  tff(c_923, plain, (![A_140, B_141]: (k1_relat_1('#skF_7'(A_140, B_141))!='#skF_9' | ~v1_funct_1('#skF_7'(A_140, B_141)) | '#skF_1'(k1_tarski(B_141), '#skF_8')=B_141 | k1_xboole_0=A_140)), inference(resolution, [status(thm)], [c_60, c_584])).
% 3.69/1.67  tff(c_965, plain, (![A_145, B_146]: (k1_relat_1('#skF_7'(A_145, B_146))!='#skF_9' | '#skF_1'(k1_tarski(B_146), '#skF_8')=B_146 | k1_xboole_0=A_145)), inference(resolution, [status(thm)], [c_58, c_923])).
% 3.69/1.67  tff(c_968, plain, (![A_26, B_30]: (A_26!='#skF_9' | '#skF_1'(k1_tarski(B_30), '#skF_8')=B_30 | k1_xboole_0=A_26 | k1_xboole_0=A_26)), inference(superposition, [status(thm), theory('equality')], [c_56, c_965])).
% 3.69/1.67  tff(c_971, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_968])).
% 3.69/1.67  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.69/1.67  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.69/1.67  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.69/1.67  tff(c_87, plain, (![C_39]: (~r1_tarski(k2_relat_1(C_39), '#skF_8') | k1_relat_1(C_39)!='#skF_9' | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.67  tff(c_90, plain, (~r1_tarski(k1_xboole_0, '#skF_8') | k1_relat_1(k1_xboole_0)!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_87])).
% 3.69/1.67  tff(c_92, plain, (k1_xboole_0!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16, c_90])).
% 3.69/1.67  tff(c_131, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_92])).
% 3.69/1.67  tff(c_48, plain, (![A_20]: (k1_relat_1('#skF_6'(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.69/1.67  tff(c_52, plain, (![A_20]: (v1_relat_1('#skF_6'(A_20)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.69/1.67  tff(c_142, plain, (![A_53]: (k1_relat_1(A_53)!=k1_xboole_0 | k1_xboole_0=A_53 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.69/1.67  tff(c_148, plain, (![A_20]: (k1_relat_1('#skF_6'(A_20))!=k1_xboole_0 | '#skF_6'(A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_142])).
% 3.69/1.67  tff(c_153, plain, (![A_54]: (k1_xboole_0!=A_54 | '#skF_6'(A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_148])).
% 3.69/1.67  tff(c_163, plain, (![A_54]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_54)), inference(superposition, [status(thm), theory('equality')], [c_153, c_52])).
% 3.69/1.67  tff(c_169, plain, (![A_54]: (k1_xboole_0!=A_54)), inference(negUnitSimplification, [status(thm)], [c_131, c_163])).
% 3.69/1.67  tff(c_34, plain, (![B_16]: (k2_zfmisc_1(k1_xboole_0, B_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.69/1.67  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_34])).
% 3.69/1.67  tff(c_181, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_92])).
% 3.69/1.67  tff(c_193, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_181])).
% 3.69/1.67  tff(c_1011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_971, c_193])).
% 3.69/1.67  tff(c_1014, plain, (![B_147]: ('#skF_1'(k1_tarski(B_147), '#skF_8')=B_147)), inference(splitRight, [status(thm)], [c_968])).
% 3.69/1.67  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.67  tff(c_1048, plain, (![B_148]: (~r2_hidden(B_148, '#skF_8') | r1_tarski(k1_tarski(B_148), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1014, c_4])).
% 3.69/1.67  tff(c_303, plain, (![B_69, A_68]: (~r1_tarski(k1_tarski(B_69), '#skF_8') | k1_relat_1('#skF_7'(A_68, B_69))!='#skF_9' | ~v1_funct_1('#skF_7'(A_68, B_69)) | ~v1_relat_1('#skF_7'(A_68, B_69)) | k1_xboole_0=A_68)), inference(superposition, [status(thm), theory('equality')], [c_297, c_62])).
% 3.69/1.67  tff(c_1178, plain, (![A_158, B_159]: (k1_relat_1('#skF_7'(A_158, B_159))!='#skF_9' | ~v1_funct_1('#skF_7'(A_158, B_159)) | ~v1_relat_1('#skF_7'(A_158, B_159)) | k1_xboole_0=A_158 | ~r2_hidden(B_159, '#skF_8'))), inference(resolution, [status(thm)], [c_1048, c_303])).
% 3.69/1.67  tff(c_1448, plain, (![A_183, B_184]: (k1_relat_1('#skF_7'(A_183, B_184))!='#skF_9' | ~v1_funct_1('#skF_7'(A_183, B_184)) | ~r2_hidden(B_184, '#skF_8') | k1_xboole_0=A_183)), inference(resolution, [status(thm)], [c_60, c_1178])).
% 3.69/1.67  tff(c_1453, plain, (![A_185, B_186]: (k1_relat_1('#skF_7'(A_185, B_186))!='#skF_9' | ~r2_hidden(B_186, '#skF_8') | k1_xboole_0=A_185)), inference(resolution, [status(thm)], [c_58, c_1448])).
% 3.69/1.67  tff(c_1456, plain, (![A_26, B_30]: (A_26!='#skF_9' | ~r2_hidden(B_30, '#skF_8') | k1_xboole_0=A_26 | k1_xboole_0=A_26)), inference(superposition, [status(thm), theory('equality')], [c_56, c_1453])).
% 3.69/1.67  tff(c_1458, plain, (![B_187]: (~r2_hidden(B_187, '#skF_8'))), inference(splitLeft, [status(thm)], [c_1456])).
% 3.69/1.67  tff(c_1486, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_531, c_1458])).
% 3.69/1.67  tff(c_1510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_1486])).
% 3.69/1.67  tff(c_1512, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1456])).
% 3.69/1.67  tff(c_1558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1512, c_193])).
% 3.69/1.67  tff(c_1560, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_181])).
% 3.69/1.67  tff(c_1559, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_181])).
% 3.69/1.67  tff(c_1579, plain, (~v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_1559])).
% 3.69/1.67  tff(c_1561, plain, (![A_188]: (k1_relat_1(A_188)!=k1_xboole_0 | k1_xboole_0=A_188 | ~v1_relat_1(A_188))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.69/1.67  tff(c_1570, plain, (![A_20]: (k1_relat_1('#skF_6'(A_20))!=k1_xboole_0 | '#skF_6'(A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_1561])).
% 3.69/1.67  tff(c_1577, plain, (![A_20]: (k1_xboole_0!=A_20 | '#skF_6'(A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1570])).
% 3.69/1.67  tff(c_1653, plain, (![A_194]: (A_194!='#skF_9' | '#skF_6'(A_194)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_1560, c_1577])).
% 3.69/1.67  tff(c_50, plain, (![A_20]: (v1_funct_1('#skF_6'(A_20)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.69/1.67  tff(c_1661, plain, (![A_194]: (v1_funct_1('#skF_9') | A_194!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1653, c_50])).
% 3.69/1.67  tff(c_1669, plain, (![A_194]: (A_194!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_1579, c_1661])).
% 3.69/1.67  tff(c_1586, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_1560, c_32])).
% 3.69/1.67  tff(c_1679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1669, c_1586])).
% 3.69/1.67  tff(c_1681, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 3.69/1.67  tff(c_1680, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_64])).
% 3.69/1.67  tff(c_1695, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_1680])).
% 3.69/1.67  tff(c_1690, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1680, c_1680, c_40])).
% 3.69/1.67  tff(c_1712, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1695, c_1690])).
% 3.69/1.67  tff(c_1689, plain, (![A_9]: (r1_tarski('#skF_9', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_1680, c_16])).
% 3.69/1.67  tff(c_1710, plain, (![A_9]: (r1_tarski('#skF_8', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1689])).
% 3.69/1.67  tff(c_1688, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1680, c_1680, c_38])).
% 3.69/1.67  tff(c_1705, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_1695, c_1688])).
% 3.69/1.67  tff(c_1742, plain, (![C_200]: (~r1_tarski(k2_relat_1(C_200), '#skF_8') | k1_relat_1(C_200)!='#skF_8' | ~v1_funct_1(C_200) | ~v1_relat_1(C_200))), inference(demodulation, [status(thm), theory('equality')], [c_1695, c_62])).
% 3.69/1.67  tff(c_1745, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1705, c_1742])).
% 3.69/1.67  tff(c_1747, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1712, c_1710, c_1745])).
% 3.69/1.67  tff(c_1748, plain, (~v1_relat_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1747])).
% 3.69/1.67  tff(c_44, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.69/1.67  tff(c_1781, plain, (![A_212]: (k1_relat_1(A_212)!='#skF_8' | A_212='#skF_8' | ~v1_relat_1(A_212))), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_1681, c_44])).
% 3.69/1.67  tff(c_1787, plain, (![A_20]: (k1_relat_1('#skF_6'(A_20))!='#skF_8' | '#skF_6'(A_20)='#skF_8')), inference(resolution, [status(thm)], [c_52, c_1781])).
% 3.69/1.67  tff(c_1792, plain, (![A_213]: (A_213!='#skF_8' | '#skF_6'(A_213)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1787])).
% 3.69/1.67  tff(c_1802, plain, (![A_213]: (v1_relat_1('#skF_8') | A_213!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1792, c_52])).
% 3.69/1.67  tff(c_1808, plain, (![A_213]: (A_213!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1748, c_1802])).
% 3.69/1.67  tff(c_1726, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_1681, c_32])).
% 3.69/1.67  tff(c_1821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1808, c_1726])).
% 3.69/1.67  tff(c_1822, plain, (~v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_1747])).
% 3.69/1.67  tff(c_1856, plain, (![A_225]: (k1_relat_1(A_225)!='#skF_8' | A_225='#skF_8' | ~v1_relat_1(A_225))), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_1681, c_44])).
% 3.69/1.67  tff(c_1865, plain, (![A_20]: (k1_relat_1('#skF_6'(A_20))!='#skF_8' | '#skF_6'(A_20)='#skF_8')), inference(resolution, [status(thm)], [c_52, c_1856])).
% 3.69/1.67  tff(c_1874, plain, (![A_226]: (A_226!='#skF_8' | '#skF_6'(A_226)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1865])).
% 3.69/1.67  tff(c_1882, plain, (![A_226]: (v1_funct_1('#skF_8') | A_226!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1874, c_50])).
% 3.69/1.67  tff(c_1890, plain, (![A_226]: (A_226!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1822, c_1882])).
% 3.69/1.67  tff(c_1922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1890, c_1726])).
% 3.69/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.67  
% 3.69/1.67  Inference rules
% 3.69/1.67  ----------------------
% 3.69/1.67  #Ref     : 0
% 3.69/1.67  #Sup     : 388
% 3.69/1.67  #Fact    : 0
% 3.69/1.67  #Define  : 0
% 3.69/1.67  #Split   : 7
% 3.69/1.67  #Chain   : 0
% 3.69/1.67  #Close   : 0
% 3.69/1.67  
% 3.69/1.67  Ordering : KBO
% 3.69/1.67  
% 3.69/1.67  Simplification rules
% 3.69/1.67  ----------------------
% 3.69/1.67  #Subsume      : 100
% 3.69/1.67  #Demod        : 278
% 3.69/1.67  #Tautology    : 198
% 3.69/1.67  #SimpNegUnit  : 68
% 3.69/1.67  #BackRed      : 137
% 3.69/1.67  
% 3.69/1.67  #Partial instantiations: 0
% 3.69/1.67  #Strategies tried      : 1
% 3.69/1.67  
% 3.69/1.67  Timing (in seconds)
% 3.69/1.67  ----------------------
% 3.69/1.67  Preprocessing        : 0.33
% 3.69/1.67  Parsing              : 0.18
% 3.69/1.67  CNF conversion       : 0.03
% 3.69/1.67  Main loop            : 0.55
% 3.69/1.67  Inferencing          : 0.20
% 3.69/1.67  Reduction            : 0.17
% 3.69/1.67  Demodulation         : 0.11
% 3.69/1.67  BG Simplification    : 0.03
% 3.69/1.67  Subsumption          : 0.10
% 3.69/1.67  Abstraction          : 0.03
% 3.69/1.67  MUC search           : 0.00
% 3.69/1.67  Cooper               : 0.00
% 3.69/1.67  Total                : 0.93
% 3.69/1.67  Index Insertion      : 0.00
% 3.69/1.67  Index Deletion       : 0.00
% 3.69/1.67  Index Matching       : 0.00
% 3.69/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
