%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:03 EST 2020

% Result     : Theorem 5.08s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 894 expanded)
%              Number of leaves         :   21 ( 325 expanded)
%              Depth                    :   20
%              Number of atoms          :  233 (2705 expanded)
%              Number of equality atoms :   94 (1145 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_63,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_28,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(c_34,plain,(
    ! [A_42,B_43] : v1_relat_1('#skF_5'(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_42,B_43] : v1_funct_1('#skF_5'(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    ! [A_42,B_43] : k1_relat_1('#skF_5'(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_336,plain,(
    ! [A_110,C_111] :
      ( r2_hidden('#skF_4'(A_110,k2_relat_1(A_110),C_111),k1_relat_1(A_110))
      | ~ r2_hidden(C_111,k2_relat_1(A_110))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_349,plain,(
    ! [A_42,B_43,C_111] :
      ( r2_hidden('#skF_4'('#skF_5'(A_42,B_43),k2_relat_1('#skF_5'(A_42,B_43)),C_111),A_42)
      | ~ r2_hidden(C_111,k2_relat_1('#skF_5'(A_42,B_43)))
      | ~ v1_funct_1('#skF_5'(A_42,B_43))
      | ~ v1_relat_1('#skF_5'(A_42,B_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_336])).

tff(c_362,plain,(
    ! [A_42,B_43,C_111] :
      ( r2_hidden('#skF_4'('#skF_5'(A_42,B_43),k2_relat_1('#skF_5'(A_42,B_43)),C_111),A_42)
      | ~ r2_hidden(C_111,k2_relat_1('#skF_5'(A_42,B_43))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_349])).

tff(c_2,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_58,plain,(
    ! [A_61] :
      ( k1_relat_1(A_61) != k1_xboole_0
      | k1_xboole_0 = A_61
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_61,plain,(
    ! [A_42,B_43] :
      ( k1_relat_1('#skF_5'(A_42,B_43)) != k1_xboole_0
      | '#skF_5'(A_42,B_43) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_58])).

tff(c_64,plain,(
    ! [B_43] : '#skF_5'(k1_xboole_0,B_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_61])).

tff(c_65,plain,(
    ! [A_62,B_63] :
      ( k1_xboole_0 != A_62
      | '#skF_5'(A_62,B_63) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_61])).

tff(c_73,plain,(
    ! [A_62] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_62 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_34])).

tff(c_82,plain,(
    ! [A_62] : k1_xboole_0 != A_62 ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2])).

tff(c_94,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_75,plain,(
    ! [A_62] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_62 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_32])).

tff(c_102,plain,(
    ! [A_62] : k1_xboole_0 != A_62 ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_2])).

tff(c_108,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_4,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_240,plain,(
    ! [A_86,D_87] :
      ( r2_hidden(k1_funct_1(A_86,D_87),k2_relat_1(A_86))
      | ~ r2_hidden(D_87,k1_relat_1(A_86))
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_248,plain,(
    ! [D_87] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_87),k1_xboole_0)
      | ~ r2_hidden(D_87,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_240])).

tff(c_253,plain,(
    ! [D_87] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_87),k1_xboole_0)
      | ~ r2_hidden(D_87,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_108,c_4,c_248])).

tff(c_28,plain,(
    ! [A_42,B_43,D_48] :
      ( k1_funct_1('#skF_5'(A_42,B_43),D_48) = B_43
      | ~ r2_hidden(D_48,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_245,plain,(
    ! [B_43,A_42,D_48] :
      ( r2_hidden(B_43,k2_relat_1('#skF_5'(A_42,B_43)))
      | ~ r2_hidden(D_48,k1_relat_1('#skF_5'(A_42,B_43)))
      | ~ v1_funct_1('#skF_5'(A_42,B_43))
      | ~ v1_relat_1('#skF_5'(A_42,B_43))
      | ~ r2_hidden(D_48,A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_240])).

tff(c_263,plain,(
    ! [B_90,A_91,D_92] :
      ( r2_hidden(B_90,k2_relat_1('#skF_5'(A_91,B_90)))
      | ~ r2_hidden(D_92,A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_245])).

tff(c_265,plain,(
    ! [B_90,D_87] :
      ( r2_hidden(B_90,k2_relat_1('#skF_5'(k1_xboole_0,B_90)))
      | ~ r2_hidden(D_87,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_253,c_263])).

tff(c_269,plain,(
    ! [B_90,D_87] :
      ( r2_hidden(B_90,k1_xboole_0)
      | ~ r2_hidden(D_87,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_64,c_265])).

tff(c_271,plain,(
    ! [D_87] : ~ r2_hidden(D_87,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_63,plain,(
    ! [A_42,B_43] :
      ( k1_xboole_0 != A_42
      | '#skF_5'(A_42,B_43) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_61])).

tff(c_936,plain,(
    ! [A_156,B_157] :
      ( r2_hidden('#skF_2'(A_156,B_157),k1_relat_1(A_156))
      | r2_hidden('#skF_3'(A_156,B_157),B_157)
      | k2_relat_1(A_156) = B_157
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_974,plain,(
    ! [B_157] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_157),k1_xboole_0)
      | r2_hidden('#skF_3'(k1_xboole_0,B_157),B_157)
      | k2_relat_1(k1_xboole_0) = B_157
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_936])).

tff(c_991,plain,(
    ! [B_157] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_157),k1_xboole_0)
      | r2_hidden('#skF_3'(k1_xboole_0,B_157),B_157)
      | k1_xboole_0 = B_157 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_108,c_2,c_974])).

tff(c_993,plain,(
    ! [B_158] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_158),B_158)
      | k1_xboole_0 = B_158 ) ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_991])).

tff(c_404,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden('#skF_4'('#skF_5'(A_117,B_118),k2_relat_1('#skF_5'(A_117,B_118)),C_119),A_117)
      | ~ r2_hidden(C_119,k2_relat_1('#skF_5'(A_117,B_118))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_349])).

tff(c_251,plain,(
    ! [B_43,A_42,D_48] :
      ( r2_hidden(B_43,k2_relat_1('#skF_5'(A_42,B_43)))
      | ~ r2_hidden(D_48,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_245])).

tff(c_447,plain,(
    ! [B_43,A_117,C_119,B_118] :
      ( r2_hidden(B_43,k2_relat_1('#skF_5'(A_117,B_43)))
      | ~ r2_hidden(C_119,k2_relat_1('#skF_5'(A_117,B_118))) ) ),
    inference(resolution,[status(thm)],[c_404,c_251])).

tff(c_1064,plain,(
    ! [B_161,A_162,B_163] :
      ( r2_hidden(B_161,k2_relat_1('#skF_5'(A_162,B_161)))
      | k2_relat_1('#skF_5'(A_162,B_163)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_993,c_447])).

tff(c_1148,plain,(
    ! [B_43,A_42,B_163] :
      ( r2_hidden(B_43,k2_relat_1(k1_xboole_0))
      | k2_relat_1('#skF_5'(A_42,B_163)) = k1_xboole_0
      | k1_xboole_0 != A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_1064])).

tff(c_1182,plain,(
    ! [B_43,A_42,B_163] :
      ( r2_hidden(B_43,k1_xboole_0)
      | k2_relat_1('#skF_5'(A_42,B_163)) = k1_xboole_0
      | k1_xboole_0 != A_42 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1148])).

tff(c_1186,plain,(
    ! [A_164,B_165] :
      ( k2_relat_1('#skF_5'(A_164,B_165)) = k1_xboole_0
      | k1_xboole_0 != A_164 ) ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_1182])).

tff(c_10,plain,(
    ! [A_2,D_41] :
      ( r2_hidden(k1_funct_1(A_2,D_41),k2_relat_1(A_2))
      | ~ r2_hidden(D_41,k1_relat_1(A_2))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1234,plain,(
    ! [A_164,B_165,D_41] :
      ( r2_hidden(k1_funct_1('#skF_5'(A_164,B_165),D_41),k1_xboole_0)
      | ~ r2_hidden(D_41,k1_relat_1('#skF_5'(A_164,B_165)))
      | ~ v1_funct_1('#skF_5'(A_164,B_165))
      | ~ v1_relat_1('#skF_5'(A_164,B_165))
      | k1_xboole_0 != A_164 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_10])).

tff(c_1270,plain,(
    ! [A_164,B_165,D_41] :
      ( r2_hidden(k1_funct_1('#skF_5'(A_164,B_165),D_41),k1_xboole_0)
      | ~ r2_hidden(D_41,A_164)
      | k1_xboole_0 != A_164 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_1234])).

tff(c_1277,plain,(
    ! [D_166,A_167] :
      ( ~ r2_hidden(D_166,A_167)
      | k1_xboole_0 != A_167 ) ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_1270])).

tff(c_1342,plain,(
    ! [C_111,B_43] : ~ r2_hidden(C_111,k2_relat_1('#skF_5'(k1_xboole_0,B_43))) ),
    inference(resolution,[status(thm)],[c_362,c_1277])).

tff(c_141,plain,(
    ! [C_75,B_76] :
      ( C_75 = B_76
      | k1_relat_1(C_75) != '#skF_6'
      | k1_relat_1(B_76) != '#skF_6'
      | ~ v1_funct_1(C_75)
      | ~ v1_relat_1(C_75)
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_145,plain,(
    ! [B_76,A_42,B_43] :
      ( B_76 = '#skF_5'(A_42,B_43)
      | k1_relat_1('#skF_5'(A_42,B_43)) != '#skF_6'
      | k1_relat_1(B_76) != '#skF_6'
      | ~ v1_funct_1('#skF_5'(A_42,B_43))
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_34,c_141])).

tff(c_153,plain,(
    ! [B_77,A_78,B_79] :
      ( B_77 = '#skF_5'(A_78,B_79)
      | A_78 != '#skF_6'
      | k1_relat_1(B_77) != '#skF_6'
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_145])).

tff(c_157,plain,(
    ! [A_78,B_79,A_42,B_43] :
      ( '#skF_5'(A_78,B_79) = '#skF_5'(A_42,B_43)
      | A_78 != '#skF_6'
      | k1_relat_1('#skF_5'(A_42,B_43)) != '#skF_6'
      | ~ v1_funct_1('#skF_5'(A_42,B_43)) ) ),
    inference(resolution,[status(thm)],[c_34,c_153])).

tff(c_163,plain,(
    ! [A_78,B_79,A_42,B_43] :
      ( '#skF_5'(A_78,B_79) = '#skF_5'(A_42,B_43)
      | A_78 != '#skF_6'
      | A_42 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_157])).

tff(c_639,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_2'(A_142,B_143),k1_relat_1(A_142))
      | r2_hidden('#skF_3'(A_142,B_143),B_143)
      | k2_relat_1(A_142) = B_143
      | ~ v1_funct_1(A_142)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_698,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_143),k1_xboole_0)
      | r2_hidden('#skF_3'(k1_xboole_0,B_143),B_143)
      | k2_relat_1(k1_xboole_0) = B_143
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_639])).

tff(c_720,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_143),k1_xboole_0)
      | r2_hidden('#skF_3'(k1_xboole_0,B_143),B_143)
      | k1_xboole_0 = B_143 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_108,c_2,c_698])).

tff(c_722,plain,(
    ! [B_144] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_144),B_144)
      | k1_xboole_0 = B_144 ) ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_720])).

tff(c_450,plain,(
    ! [B_120,A_121,C_122,B_123] :
      ( r2_hidden(B_120,k2_relat_1('#skF_5'(A_121,B_120)))
      | ~ r2_hidden(C_122,k2_relat_1('#skF_5'(A_121,B_123))) ) ),
    inference(resolution,[status(thm)],[c_404,c_251])).

tff(c_461,plain,(
    ! [A_42,B_79,C_122,A_78,B_120] :
      ( r2_hidden(B_120,k2_relat_1('#skF_5'(A_42,B_120)))
      | ~ r2_hidden(C_122,k2_relat_1('#skF_5'(A_78,B_79)))
      | A_78 != '#skF_6'
      | A_42 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_450])).

tff(c_506,plain,(
    ! [C_129,A_130,B_131] :
      ( ~ r2_hidden(C_129,k2_relat_1('#skF_5'(A_130,B_131)))
      | A_130 != '#skF_6' ) ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_518,plain,(
    ! [A_130,D_41,B_131] :
      ( A_130 != '#skF_6'
      | ~ r2_hidden(D_41,k1_relat_1('#skF_5'(A_130,B_131)))
      | ~ v1_funct_1('#skF_5'(A_130,B_131))
      | ~ v1_relat_1('#skF_5'(A_130,B_131)) ) ),
    inference(resolution,[status(thm)],[c_10,c_506])).

tff(c_532,plain,(
    ! [A_130,D_41] :
      ( A_130 != '#skF_6'
      | ~ r2_hidden(D_41,A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_518])).

tff(c_778,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_722,c_532])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_36])).

tff(c_797,plain,(
    ! [B_145,A_146] :
      ( r2_hidden(B_145,k2_relat_1('#skF_5'(A_146,B_145)))
      | A_146 != '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_815,plain,(
    ! [B_43,A_78,B_79,A_42] :
      ( r2_hidden(B_43,k2_relat_1('#skF_5'(A_78,B_79)))
      | A_42 != '#skF_6'
      | A_78 != '#skF_6'
      | A_42 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_797])).

tff(c_833,plain,(
    ! [A_42] :
      ( A_42 != '#skF_6'
      | A_42 != '#skF_6' ) ),
    inference(splitLeft,[status(thm)],[c_815])).

tff(c_839,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_833])).

tff(c_840,plain,(
    ! [B_43,A_78,B_79] :
      ( r2_hidden(B_43,k2_relat_1('#skF_5'(A_78,B_79)))
      | A_78 != '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_815])).

tff(c_274,plain,(
    ! [A_94,C_95] :
      ( k1_funct_1(A_94,'#skF_4'(A_94,k2_relat_1(A_94),C_95)) = C_95
      | ~ r2_hidden(C_95,k2_relat_1(A_94))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_284,plain,(
    ! [C_95,B_43,A_42] :
      ( C_95 = B_43
      | ~ r2_hidden('#skF_4'('#skF_5'(A_42,B_43),k2_relat_1('#skF_5'(A_42,B_43)),C_95),A_42)
      | ~ r2_hidden(C_95,k2_relat_1('#skF_5'(A_42,B_43)))
      | ~ v1_funct_1('#skF_5'(A_42,B_43))
      | ~ v1_relat_1('#skF_5'(A_42,B_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_28])).

tff(c_3363,plain,(
    ! [C_238,B_239,A_240] :
      ( C_238 = B_239
      | ~ r2_hidden('#skF_4'('#skF_5'(A_240,B_239),k2_relat_1('#skF_5'(A_240,B_239)),C_238),A_240)
      | ~ r2_hidden(C_238,k2_relat_1('#skF_5'(A_240,B_239))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_284])).

tff(c_3429,plain,(
    ! [C_241,B_242,A_243] :
      ( C_241 = B_242
      | ~ r2_hidden(C_241,k2_relat_1('#skF_5'(A_243,B_242))) ) ),
    inference(resolution,[status(thm)],[c_362,c_3363])).

tff(c_3524,plain,(
    ! [B_79,B_43,A_78] :
      ( B_79 = B_43
      | A_78 != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_840,c_3429])).

tff(c_3531,plain,(
    ! [A_78] : A_78 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3524])).

tff(c_3535,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3531])).

tff(c_3648,plain,(
    ! [B_244] : k1_xboole_0 = B_244 ),
    inference(splitRight,[status(thm)],[c_3524])).

tff(c_829,plain,(
    ! [B_43,A_146,B_145] :
      ( r2_hidden(B_43,k2_relat_1('#skF_5'(k2_relat_1('#skF_5'(A_146,B_145)),B_43)))
      | A_146 != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_797,c_251])).

tff(c_3650,plain,(
    ! [B_43,A_146] :
      ( r2_hidden(B_43,k2_relat_1('#skF_5'(k1_xboole_0,B_43)))
      | A_146 != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3648,c_829])).

tff(c_5456,plain,(
    ! [A_146] : A_146 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1342,c_3650])).

tff(c_5481,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5456])).

tff(c_5485,plain,(
    ! [B_1204] : r2_hidden(B_1204,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_121,plain,(
    ! [A_67,B_68,D_69] :
      ( k1_funct_1('#skF_5'(A_67,B_68),D_69) = B_68
      | ~ r2_hidden(D_69,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_130,plain,(
    ! [D_69,B_43,A_42] :
      ( k1_funct_1(k1_xboole_0,D_69) = B_43
      | ~ r2_hidden(D_69,A_42)
      | k1_xboole_0 != A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_121])).

tff(c_5528,plain,(
    ! [B_1205] : k1_funct_1(k1_xboole_0,B_1205) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5485,c_130])).

tff(c_5492,plain,(
    ! [B_1204,B_43] : k1_funct_1(k1_xboole_0,B_1204) = B_43 ),
    inference(resolution,[status(thm)],[c_5485,c_130])).

tff(c_5858,plain,(
    ! [B_1870] : B_1870 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_5528,c_5492])).

tff(c_5904,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5858,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.08/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.98  
% 5.08/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/1.98  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5
% 5.45/1.98  
% 5.45/1.98  %Foreground sorts:
% 5.45/1.98  
% 5.45/1.98  
% 5.45/1.98  %Background operators:
% 5.45/1.98  
% 5.45/1.98  
% 5.45/1.98  %Foreground operators:
% 5.45/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.45/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.45/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.45/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.45/1.98  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.45/1.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.45/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.45/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.45/1.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.45/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.45/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.45/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.45/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.45/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.45/1.98  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.45/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.45/1.98  
% 5.45/2.00  tff(f_63, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 5.45/2.00  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 5.45/2.00  tff(f_28, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.45/2.00  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.45/2.00  tff(f_82, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 5.45/2.00  tff(c_34, plain, (![A_42, B_43]: (v1_relat_1('#skF_5'(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.00  tff(c_32, plain, (![A_42, B_43]: (v1_funct_1('#skF_5'(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.00  tff(c_30, plain, (![A_42, B_43]: (k1_relat_1('#skF_5'(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.00  tff(c_336, plain, (![A_110, C_111]: (r2_hidden('#skF_4'(A_110, k2_relat_1(A_110), C_111), k1_relat_1(A_110)) | ~r2_hidden(C_111, k2_relat_1(A_110)) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.45/2.00  tff(c_349, plain, (![A_42, B_43, C_111]: (r2_hidden('#skF_4'('#skF_5'(A_42, B_43), k2_relat_1('#skF_5'(A_42, B_43)), C_111), A_42) | ~r2_hidden(C_111, k2_relat_1('#skF_5'(A_42, B_43))) | ~v1_funct_1('#skF_5'(A_42, B_43)) | ~v1_relat_1('#skF_5'(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_336])).
% 5.45/2.00  tff(c_362, plain, (![A_42, B_43, C_111]: (r2_hidden('#skF_4'('#skF_5'(A_42, B_43), k2_relat_1('#skF_5'(A_42, B_43)), C_111), A_42) | ~r2_hidden(C_111, k2_relat_1('#skF_5'(A_42, B_43))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_349])).
% 5.45/2.00  tff(c_2, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.45/2.00  tff(c_58, plain, (![A_61]: (k1_relat_1(A_61)!=k1_xboole_0 | k1_xboole_0=A_61 | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.45/2.00  tff(c_61, plain, (![A_42, B_43]: (k1_relat_1('#skF_5'(A_42, B_43))!=k1_xboole_0 | '#skF_5'(A_42, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_58])).
% 5.45/2.00  tff(c_64, plain, (![B_43]: ('#skF_5'(k1_xboole_0, B_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_61])).
% 5.45/2.00  tff(c_65, plain, (![A_62, B_63]: (k1_xboole_0!=A_62 | '#skF_5'(A_62, B_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_61])).
% 5.45/2.00  tff(c_73, plain, (![A_62]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_62)), inference(superposition, [status(thm), theory('equality')], [c_65, c_34])).
% 5.45/2.00  tff(c_82, plain, (![A_62]: (k1_xboole_0!=A_62)), inference(splitLeft, [status(thm)], [c_73])).
% 5.45/2.00  tff(c_93, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_2])).
% 5.45/2.00  tff(c_94, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_73])).
% 5.45/2.00  tff(c_75, plain, (![A_62]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_62)), inference(superposition, [status(thm), theory('equality')], [c_65, c_32])).
% 5.45/2.00  tff(c_102, plain, (![A_62]: (k1_xboole_0!=A_62)), inference(splitLeft, [status(thm)], [c_75])).
% 5.45/2.00  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_2])).
% 5.45/2.00  tff(c_108, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_75])).
% 5.45/2.00  tff(c_4, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.45/2.00  tff(c_240, plain, (![A_86, D_87]: (r2_hidden(k1_funct_1(A_86, D_87), k2_relat_1(A_86)) | ~r2_hidden(D_87, k1_relat_1(A_86)) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.45/2.00  tff(c_248, plain, (![D_87]: (r2_hidden(k1_funct_1(k1_xboole_0, D_87), k1_xboole_0) | ~r2_hidden(D_87, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_240])).
% 5.45/2.00  tff(c_253, plain, (![D_87]: (r2_hidden(k1_funct_1(k1_xboole_0, D_87), k1_xboole_0) | ~r2_hidden(D_87, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_108, c_4, c_248])).
% 5.45/2.00  tff(c_28, plain, (![A_42, B_43, D_48]: (k1_funct_1('#skF_5'(A_42, B_43), D_48)=B_43 | ~r2_hidden(D_48, A_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.00  tff(c_245, plain, (![B_43, A_42, D_48]: (r2_hidden(B_43, k2_relat_1('#skF_5'(A_42, B_43))) | ~r2_hidden(D_48, k1_relat_1('#skF_5'(A_42, B_43))) | ~v1_funct_1('#skF_5'(A_42, B_43)) | ~v1_relat_1('#skF_5'(A_42, B_43)) | ~r2_hidden(D_48, A_42))), inference(superposition, [status(thm), theory('equality')], [c_28, c_240])).
% 5.45/2.00  tff(c_263, plain, (![B_90, A_91, D_92]: (r2_hidden(B_90, k2_relat_1('#skF_5'(A_91, B_90))) | ~r2_hidden(D_92, A_91))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_245])).
% 5.45/2.00  tff(c_265, plain, (![B_90, D_87]: (r2_hidden(B_90, k2_relat_1('#skF_5'(k1_xboole_0, B_90))) | ~r2_hidden(D_87, k1_xboole_0))), inference(resolution, [status(thm)], [c_253, c_263])).
% 5.45/2.00  tff(c_269, plain, (![B_90, D_87]: (r2_hidden(B_90, k1_xboole_0) | ~r2_hidden(D_87, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_64, c_265])).
% 5.45/2.00  tff(c_271, plain, (![D_87]: (~r2_hidden(D_87, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_269])).
% 5.45/2.00  tff(c_63, plain, (![A_42, B_43]: (k1_xboole_0!=A_42 | '#skF_5'(A_42, B_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_61])).
% 5.45/2.00  tff(c_936, plain, (![A_156, B_157]: (r2_hidden('#skF_2'(A_156, B_157), k1_relat_1(A_156)) | r2_hidden('#skF_3'(A_156, B_157), B_157) | k2_relat_1(A_156)=B_157 | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.45/2.00  tff(c_974, plain, (![B_157]: (r2_hidden('#skF_2'(k1_xboole_0, B_157), k1_xboole_0) | r2_hidden('#skF_3'(k1_xboole_0, B_157), B_157) | k2_relat_1(k1_xboole_0)=B_157 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_936])).
% 5.45/2.00  tff(c_991, plain, (![B_157]: (r2_hidden('#skF_2'(k1_xboole_0, B_157), k1_xboole_0) | r2_hidden('#skF_3'(k1_xboole_0, B_157), B_157) | k1_xboole_0=B_157)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_108, c_2, c_974])).
% 5.45/2.00  tff(c_993, plain, (![B_158]: (r2_hidden('#skF_3'(k1_xboole_0, B_158), B_158) | k1_xboole_0=B_158)), inference(negUnitSimplification, [status(thm)], [c_271, c_991])).
% 5.45/2.00  tff(c_404, plain, (![A_117, B_118, C_119]: (r2_hidden('#skF_4'('#skF_5'(A_117, B_118), k2_relat_1('#skF_5'(A_117, B_118)), C_119), A_117) | ~r2_hidden(C_119, k2_relat_1('#skF_5'(A_117, B_118))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_349])).
% 5.45/2.00  tff(c_251, plain, (![B_43, A_42, D_48]: (r2_hidden(B_43, k2_relat_1('#skF_5'(A_42, B_43))) | ~r2_hidden(D_48, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_245])).
% 5.45/2.00  tff(c_447, plain, (![B_43, A_117, C_119, B_118]: (r2_hidden(B_43, k2_relat_1('#skF_5'(A_117, B_43))) | ~r2_hidden(C_119, k2_relat_1('#skF_5'(A_117, B_118))))), inference(resolution, [status(thm)], [c_404, c_251])).
% 5.45/2.00  tff(c_1064, plain, (![B_161, A_162, B_163]: (r2_hidden(B_161, k2_relat_1('#skF_5'(A_162, B_161))) | k2_relat_1('#skF_5'(A_162, B_163))=k1_xboole_0)), inference(resolution, [status(thm)], [c_993, c_447])).
% 5.45/2.00  tff(c_1148, plain, (![B_43, A_42, B_163]: (r2_hidden(B_43, k2_relat_1(k1_xboole_0)) | k2_relat_1('#skF_5'(A_42, B_163))=k1_xboole_0 | k1_xboole_0!=A_42)), inference(superposition, [status(thm), theory('equality')], [c_63, c_1064])).
% 5.45/2.00  tff(c_1182, plain, (![B_43, A_42, B_163]: (r2_hidden(B_43, k1_xboole_0) | k2_relat_1('#skF_5'(A_42, B_163))=k1_xboole_0 | k1_xboole_0!=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1148])).
% 5.45/2.00  tff(c_1186, plain, (![A_164, B_165]: (k2_relat_1('#skF_5'(A_164, B_165))=k1_xboole_0 | k1_xboole_0!=A_164)), inference(negUnitSimplification, [status(thm)], [c_271, c_1182])).
% 5.45/2.00  tff(c_10, plain, (![A_2, D_41]: (r2_hidden(k1_funct_1(A_2, D_41), k2_relat_1(A_2)) | ~r2_hidden(D_41, k1_relat_1(A_2)) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.45/2.00  tff(c_1234, plain, (![A_164, B_165, D_41]: (r2_hidden(k1_funct_1('#skF_5'(A_164, B_165), D_41), k1_xboole_0) | ~r2_hidden(D_41, k1_relat_1('#skF_5'(A_164, B_165))) | ~v1_funct_1('#skF_5'(A_164, B_165)) | ~v1_relat_1('#skF_5'(A_164, B_165)) | k1_xboole_0!=A_164)), inference(superposition, [status(thm), theory('equality')], [c_1186, c_10])).
% 5.45/2.00  tff(c_1270, plain, (![A_164, B_165, D_41]: (r2_hidden(k1_funct_1('#skF_5'(A_164, B_165), D_41), k1_xboole_0) | ~r2_hidden(D_41, A_164) | k1_xboole_0!=A_164)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_1234])).
% 5.45/2.00  tff(c_1277, plain, (![D_166, A_167]: (~r2_hidden(D_166, A_167) | k1_xboole_0!=A_167)), inference(negUnitSimplification, [status(thm)], [c_271, c_1270])).
% 5.45/2.00  tff(c_1342, plain, (![C_111, B_43]: (~r2_hidden(C_111, k2_relat_1('#skF_5'(k1_xboole_0, B_43))))), inference(resolution, [status(thm)], [c_362, c_1277])).
% 5.45/2.00  tff(c_141, plain, (![C_75, B_76]: (C_75=B_76 | k1_relat_1(C_75)!='#skF_6' | k1_relat_1(B_76)!='#skF_6' | ~v1_funct_1(C_75) | ~v1_relat_1(C_75) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.45/2.00  tff(c_145, plain, (![B_76, A_42, B_43]: (B_76='#skF_5'(A_42, B_43) | k1_relat_1('#skF_5'(A_42, B_43))!='#skF_6' | k1_relat_1(B_76)!='#skF_6' | ~v1_funct_1('#skF_5'(A_42, B_43)) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_34, c_141])).
% 5.45/2.00  tff(c_153, plain, (![B_77, A_78, B_79]: (B_77='#skF_5'(A_78, B_79) | A_78!='#skF_6' | k1_relat_1(B_77)!='#skF_6' | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_145])).
% 5.45/2.00  tff(c_157, plain, (![A_78, B_79, A_42, B_43]: ('#skF_5'(A_78, B_79)='#skF_5'(A_42, B_43) | A_78!='#skF_6' | k1_relat_1('#skF_5'(A_42, B_43))!='#skF_6' | ~v1_funct_1('#skF_5'(A_42, B_43)))), inference(resolution, [status(thm)], [c_34, c_153])).
% 5.45/2.00  tff(c_163, plain, (![A_78, B_79, A_42, B_43]: ('#skF_5'(A_78, B_79)='#skF_5'(A_42, B_43) | A_78!='#skF_6' | A_42!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_157])).
% 5.45/2.00  tff(c_639, plain, (![A_142, B_143]: (r2_hidden('#skF_2'(A_142, B_143), k1_relat_1(A_142)) | r2_hidden('#skF_3'(A_142, B_143), B_143) | k2_relat_1(A_142)=B_143 | ~v1_funct_1(A_142) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.45/2.00  tff(c_698, plain, (![B_143]: (r2_hidden('#skF_2'(k1_xboole_0, B_143), k1_xboole_0) | r2_hidden('#skF_3'(k1_xboole_0, B_143), B_143) | k2_relat_1(k1_xboole_0)=B_143 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_639])).
% 5.45/2.00  tff(c_720, plain, (![B_143]: (r2_hidden('#skF_2'(k1_xboole_0, B_143), k1_xboole_0) | r2_hidden('#skF_3'(k1_xboole_0, B_143), B_143) | k1_xboole_0=B_143)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_108, c_2, c_698])).
% 5.45/2.00  tff(c_722, plain, (![B_144]: (r2_hidden('#skF_3'(k1_xboole_0, B_144), B_144) | k1_xboole_0=B_144)), inference(negUnitSimplification, [status(thm)], [c_271, c_720])).
% 5.45/2.00  tff(c_450, plain, (![B_120, A_121, C_122, B_123]: (r2_hidden(B_120, k2_relat_1('#skF_5'(A_121, B_120))) | ~r2_hidden(C_122, k2_relat_1('#skF_5'(A_121, B_123))))), inference(resolution, [status(thm)], [c_404, c_251])).
% 5.45/2.00  tff(c_461, plain, (![A_42, B_79, C_122, A_78, B_120]: (r2_hidden(B_120, k2_relat_1('#skF_5'(A_42, B_120))) | ~r2_hidden(C_122, k2_relat_1('#skF_5'(A_78, B_79))) | A_78!='#skF_6' | A_42!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_163, c_450])).
% 5.45/2.00  tff(c_506, plain, (![C_129, A_130, B_131]: (~r2_hidden(C_129, k2_relat_1('#skF_5'(A_130, B_131))) | A_130!='#skF_6')), inference(splitLeft, [status(thm)], [c_461])).
% 5.45/2.00  tff(c_518, plain, (![A_130, D_41, B_131]: (A_130!='#skF_6' | ~r2_hidden(D_41, k1_relat_1('#skF_5'(A_130, B_131))) | ~v1_funct_1('#skF_5'(A_130, B_131)) | ~v1_relat_1('#skF_5'(A_130, B_131)))), inference(resolution, [status(thm)], [c_10, c_506])).
% 5.45/2.00  tff(c_532, plain, (![A_130, D_41]: (A_130!='#skF_6' | ~r2_hidden(D_41, A_130))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_518])).
% 5.45/2.00  tff(c_778, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_722, c_532])).
% 5.45/2.00  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.45/2.00  tff(c_794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_778, c_36])).
% 5.45/2.00  tff(c_797, plain, (![B_145, A_146]: (r2_hidden(B_145, k2_relat_1('#skF_5'(A_146, B_145))) | A_146!='#skF_6')), inference(splitRight, [status(thm)], [c_461])).
% 5.45/2.00  tff(c_815, plain, (![B_43, A_78, B_79, A_42]: (r2_hidden(B_43, k2_relat_1('#skF_5'(A_78, B_79))) | A_42!='#skF_6' | A_78!='#skF_6' | A_42!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_163, c_797])).
% 5.45/2.00  tff(c_833, plain, (![A_42]: (A_42!='#skF_6' | A_42!='#skF_6')), inference(splitLeft, [status(thm)], [c_815])).
% 5.45/2.00  tff(c_839, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_833])).
% 5.45/2.00  tff(c_840, plain, (![B_43, A_78, B_79]: (r2_hidden(B_43, k2_relat_1('#skF_5'(A_78, B_79))) | A_78!='#skF_6')), inference(splitRight, [status(thm)], [c_815])).
% 5.45/2.00  tff(c_274, plain, (![A_94, C_95]: (k1_funct_1(A_94, '#skF_4'(A_94, k2_relat_1(A_94), C_95))=C_95 | ~r2_hidden(C_95, k2_relat_1(A_94)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.45/2.00  tff(c_284, plain, (![C_95, B_43, A_42]: (C_95=B_43 | ~r2_hidden('#skF_4'('#skF_5'(A_42, B_43), k2_relat_1('#skF_5'(A_42, B_43)), C_95), A_42) | ~r2_hidden(C_95, k2_relat_1('#skF_5'(A_42, B_43))) | ~v1_funct_1('#skF_5'(A_42, B_43)) | ~v1_relat_1('#skF_5'(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_274, c_28])).
% 5.45/2.00  tff(c_3363, plain, (![C_238, B_239, A_240]: (C_238=B_239 | ~r2_hidden('#skF_4'('#skF_5'(A_240, B_239), k2_relat_1('#skF_5'(A_240, B_239)), C_238), A_240) | ~r2_hidden(C_238, k2_relat_1('#skF_5'(A_240, B_239))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_284])).
% 5.45/2.00  tff(c_3429, plain, (![C_241, B_242, A_243]: (C_241=B_242 | ~r2_hidden(C_241, k2_relat_1('#skF_5'(A_243, B_242))))), inference(resolution, [status(thm)], [c_362, c_3363])).
% 5.45/2.00  tff(c_3524, plain, (![B_79, B_43, A_78]: (B_79=B_43 | A_78!='#skF_6')), inference(resolution, [status(thm)], [c_840, c_3429])).
% 5.45/2.00  tff(c_3531, plain, (![A_78]: (A_78!='#skF_6')), inference(splitLeft, [status(thm)], [c_3524])).
% 5.45/2.00  tff(c_3535, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_3531])).
% 5.45/2.00  tff(c_3648, plain, (![B_244]: (k1_xboole_0=B_244)), inference(splitRight, [status(thm)], [c_3524])).
% 5.45/2.00  tff(c_829, plain, (![B_43, A_146, B_145]: (r2_hidden(B_43, k2_relat_1('#skF_5'(k2_relat_1('#skF_5'(A_146, B_145)), B_43))) | A_146!='#skF_6')), inference(resolution, [status(thm)], [c_797, c_251])).
% 5.45/2.00  tff(c_3650, plain, (![B_43, A_146]: (r2_hidden(B_43, k2_relat_1('#skF_5'(k1_xboole_0, B_43))) | A_146!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3648, c_829])).
% 5.45/2.00  tff(c_5456, plain, (![A_146]: (A_146!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1342, c_3650])).
% 5.45/2.00  tff(c_5481, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_5456])).
% 5.45/2.00  tff(c_5485, plain, (![B_1204]: (r2_hidden(B_1204, k1_xboole_0))), inference(splitRight, [status(thm)], [c_269])).
% 5.45/2.00  tff(c_121, plain, (![A_67, B_68, D_69]: (k1_funct_1('#skF_5'(A_67, B_68), D_69)=B_68 | ~r2_hidden(D_69, A_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.45/2.00  tff(c_130, plain, (![D_69, B_43, A_42]: (k1_funct_1(k1_xboole_0, D_69)=B_43 | ~r2_hidden(D_69, A_42) | k1_xboole_0!=A_42)), inference(superposition, [status(thm), theory('equality')], [c_63, c_121])).
% 5.45/2.00  tff(c_5528, plain, (![B_1205]: (k1_funct_1(k1_xboole_0, B_1205)='#skF_6')), inference(resolution, [status(thm)], [c_5485, c_130])).
% 5.45/2.00  tff(c_5492, plain, (![B_1204, B_43]: (k1_funct_1(k1_xboole_0, B_1204)=B_43)), inference(resolution, [status(thm)], [c_5485, c_130])).
% 5.45/2.00  tff(c_5858, plain, (![B_1870]: (B_1870='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5528, c_5492])).
% 5.45/2.00  tff(c_5904, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5858, c_36])).
% 5.45/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/2.00  
% 5.45/2.00  Inference rules
% 5.45/2.00  ----------------------
% 5.45/2.00  #Ref     : 6
% 5.45/2.00  #Sup     : 1364
% 5.45/2.00  #Fact    : 0
% 5.45/2.00  #Define  : 0
% 5.45/2.00  #Split   : 9
% 5.45/2.00  #Chain   : 0
% 5.45/2.00  #Close   : 0
% 5.45/2.00  
% 5.45/2.00  Ordering : KBO
% 5.45/2.00  
% 5.45/2.00  Simplification rules
% 5.45/2.00  ----------------------
% 5.45/2.00  #Subsume      : 576
% 5.45/2.00  #Demod        : 697
% 5.45/2.00  #Tautology    : 187
% 5.45/2.00  #SimpNegUnit  : 104
% 5.45/2.00  #BackRed      : 18
% 5.45/2.00  
% 5.45/2.00  #Partial instantiations: 900
% 5.45/2.00  #Strategies tried      : 1
% 5.45/2.00  
% 5.45/2.00  Timing (in seconds)
% 5.45/2.00  ----------------------
% 5.57/2.00  Preprocessing        : 0.32
% 5.57/2.00  Parsing              : 0.16
% 5.57/2.00  CNF conversion       : 0.03
% 5.57/2.00  Main loop            : 0.91
% 5.57/2.00  Inferencing          : 0.31
% 5.57/2.00  Reduction            : 0.32
% 5.57/2.00  Demodulation         : 0.22
% 5.57/2.00  BG Simplification    : 0.04
% 5.57/2.00  Subsumption          : 0.19
% 5.57/2.00  Abstraction          : 0.05
% 5.57/2.00  MUC search           : 0.00
% 5.57/2.00  Cooper               : 0.00
% 5.57/2.00  Total                : 1.27
% 5.57/2.00  Index Insertion      : 0.00
% 5.57/2.00  Index Deletion       : 0.00
% 5.57/2.01  Index Matching       : 0.00
% 5.57/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
