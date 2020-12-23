%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:03 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  166 (2910 expanded)
%              Number of leaves         :   22 (1047 expanded)
%              Depth                    :   17
%              Number of atoms          :  326 (9640 expanded)
%              Number of equality atoms :  174 (3731 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_72,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_91,negated_conjecture,(
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

tff(f_48,axiom,(
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

tff(c_34,plain,(
    ! [A_49] : k1_relat_1('#skF_6'(A_49)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    ! [A_49] : v1_relat_1('#skF_6'(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_65,plain,(
    ! [A_70] :
      ( k1_relat_1(A_70) != k1_xboole_0
      | k1_xboole_0 = A_70
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_49] :
      ( k1_relat_1('#skF_6'(A_49)) != k1_xboole_0
      | '#skF_6'(A_49) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_77,plain,(
    ! [A_71] :
      ( k1_xboole_0 != A_71
      | '#skF_6'(A_71) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_71])).

tff(c_142,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_34])).

tff(c_26,plain,(
    ! [A_42,B_43] : k1_relat_1('#skF_5'(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [A_42,B_43] : v1_relat_1('#skF_5'(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_68,plain,(
    ! [A_42,B_43] :
      ( k1_relat_1('#skF_5'(A_42,B_43)) != k1_xboole_0
      | '#skF_5'(A_42,B_43) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_73,plain,(
    ! [A_42,B_43] :
      ( k1_xboole_0 != A_42
      | '#skF_5'(A_42,B_43) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_28,plain,(
    ! [A_42,B_43] : v1_funct_1('#skF_5'(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ! [A_49] : v1_funct_1('#skF_6'(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_93,plain,(
    ! [C_72,B_73] :
      ( C_72 = B_73
      | k1_relat_1(C_72) != '#skF_7'
      | k1_relat_1(B_73) != '#skF_7'
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72)
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_97,plain,(
    ! [B_73,A_49] :
      ( B_73 = '#skF_6'(A_49)
      | k1_relat_1('#skF_6'(A_49)) != '#skF_7'
      | k1_relat_1(B_73) != '#skF_7'
      | ~ v1_funct_1('#skF_6'(A_49))
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_38,c_93])).

tff(c_233,plain,(
    ! [B_98,A_99] :
      ( B_98 = '#skF_6'(A_99)
      | A_99 != '#skF_7'
      | k1_relat_1(B_98) != '#skF_7'
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_97])).

tff(c_237,plain,(
    ! [A_99,A_42,B_43] :
      ( '#skF_6'(A_99) = '#skF_5'(A_42,B_43)
      | A_99 != '#skF_7'
      | k1_relat_1('#skF_5'(A_42,B_43)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_42,B_43)) ) ),
    inference(resolution,[status(thm)],[c_30,c_233])).

tff(c_245,plain,(
    ! [A_99,A_42,B_43] :
      ( '#skF_6'(A_99) = '#skF_5'(A_42,B_43)
      | A_99 != '#skF_7'
      | A_42 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_237])).

tff(c_680,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_2'(A_137,B_138),k1_relat_1(A_137))
      | r2_hidden('#skF_3'(A_137,B_138),B_138)
      | k2_relat_1(A_137) = B_138
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_709,plain,(
    ! [A_49,B_138] :
      ( r2_hidden('#skF_2'('#skF_6'(A_49),B_138),A_49)
      | r2_hidden('#skF_3'('#skF_6'(A_49),B_138),B_138)
      | k2_relat_1('#skF_6'(A_49)) = B_138
      | ~ v1_funct_1('#skF_6'(A_49))
      | ~ v1_relat_1('#skF_6'(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_680])).

tff(c_2611,plain,(
    ! [A_228,B_229] :
      ( r2_hidden('#skF_2'('#skF_6'(A_228),B_229),A_228)
      | r2_hidden('#skF_3'('#skF_6'(A_228),B_229),B_229)
      | k2_relat_1('#skF_6'(A_228)) = B_229 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_709])).

tff(c_85,plain,(
    ! [A_71] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_71 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_38])).

tff(c_104,plain,(
    ! [A_71] : k1_xboole_0 != A_71 ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_110,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_104])).

tff(c_111,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_87,plain,(
    ! [A_71] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_71 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_36])).

tff(c_120,plain,(
    ! [A_71] : k1_xboole_0 != A_71 ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_126,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_120])).

tff(c_127,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_6,plain,(
    ! [A_2,D_41] :
      ( r2_hidden(k1_funct_1(A_2,D_41),k2_relat_1(A_2))
      | ~ r2_hidden(D_41,k1_relat_1(A_2))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_49] :
      ( k1_xboole_0 != A_49
      | '#skF_6'(A_49) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_71])).

tff(c_535,plain,(
    ! [A_117,C_118] :
      ( r2_hidden('#skF_4'(A_117,k2_relat_1(A_117),C_118),k1_relat_1(A_117))
      | ~ r2_hidden(C_118,k2_relat_1(A_117))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_547,plain,(
    ! [A_49,C_118] :
      ( r2_hidden('#skF_4'('#skF_6'(A_49),k2_relat_1('#skF_6'(A_49)),C_118),A_49)
      | ~ r2_hidden(C_118,k2_relat_1('#skF_6'(A_49)))
      | ~ v1_funct_1('#skF_6'(A_49))
      | ~ v1_relat_1('#skF_6'(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_535])).

tff(c_617,plain,(
    ! [A_133,C_134] :
      ( r2_hidden('#skF_4'('#skF_6'(A_133),k2_relat_1('#skF_6'(A_133)),C_134),A_133)
      | ~ r2_hidden(C_134,k2_relat_1('#skF_6'(A_133))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_547])).

tff(c_32,plain,(
    ! [A_49,C_54] :
      ( k1_funct_1('#skF_6'(A_49),C_54) = k1_xboole_0
      | ~ r2_hidden(C_54,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_204,plain,(
    ! [A_88,D_89] :
      ( r2_hidden(k1_funct_1(A_88,D_89),k2_relat_1(A_88))
      | ~ r2_hidden(D_89,k1_relat_1(A_88))
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_213,plain,(
    ! [A_49,C_54] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(A_49)))
      | ~ r2_hidden(C_54,k1_relat_1('#skF_6'(A_49)))
      | ~ v1_funct_1('#skF_6'(A_49))
      | ~ v1_relat_1('#skF_6'(A_49))
      | ~ r2_hidden(C_54,A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_204])).

tff(c_218,plain,(
    ! [A_49,C_54] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(A_49)))
      | ~ r2_hidden(C_54,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_213])).

tff(c_657,plain,(
    ! [A_135,C_136] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(A_135)))
      | ~ r2_hidden(C_136,k2_relat_1('#skF_6'(A_135))) ) ),
    inference(resolution,[status(thm)],[c_617,c_218])).

tff(c_674,plain,(
    ! [A_49,C_136] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(A_49)))
      | ~ r2_hidden(C_136,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_657])).

tff(c_753,plain,(
    ! [C_142] : ~ r2_hidden(C_142,k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_674])).

tff(c_769,plain,(
    ! [D_41] :
      ( ~ r2_hidden(D_41,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_753])).

tff(c_775,plain,(
    ! [D_41] : ~ r2_hidden(D_41,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_127,c_142,c_769])).

tff(c_2947,plain,(
    ! [A_230] :
      ( r2_hidden('#skF_2'('#skF_6'(A_230),k1_xboole_0),A_230)
      | k2_relat_1('#skF_6'(A_230)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2611,c_775])).

tff(c_239,plain,(
    ! [A_99,A_49] :
      ( '#skF_6'(A_99) = '#skF_6'(A_49)
      | A_99 != '#skF_7'
      | k1_relat_1('#skF_6'(A_49)) != '#skF_7'
      | ~ v1_funct_1('#skF_6'(A_49)) ) ),
    inference(resolution,[status(thm)],[c_38,c_233])).

tff(c_248,plain,(
    ! [A_99,A_49] :
      ( '#skF_6'(A_99) = '#skF_6'(A_49)
      | A_99 != '#skF_7'
      | A_49 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_239])).

tff(c_667,plain,(
    ! [A_49,C_136,A_99] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(A_49)))
      | ~ r2_hidden(C_136,k2_relat_1('#skF_6'(A_99)))
      | A_99 != '#skF_7'
      | A_49 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_657])).

tff(c_827,plain,(
    ! [C_145,A_146] :
      ( ~ r2_hidden(C_145,k2_relat_1('#skF_6'(A_146)))
      | A_146 != '#skF_7' ) ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_852,plain,(
    ! [A_146,D_41] :
      ( A_146 != '#skF_7'
      | ~ r2_hidden(D_41,k1_relat_1('#skF_6'(A_146)))
      | ~ v1_funct_1('#skF_6'(A_146))
      | ~ v1_relat_1('#skF_6'(A_146)) ) ),
    inference(resolution,[status(thm)],[c_6,c_827])).

tff(c_861,plain,(
    ! [A_146,D_41] :
      ( A_146 != '#skF_7'
      | ~ r2_hidden(D_41,A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_852])).

tff(c_3311,plain,(
    ! [A_233] :
      ( A_233 != '#skF_7'
      | k2_relat_1('#skF_6'(A_233)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2947,c_861])).

tff(c_250,plain,(
    ! [A_101,A_100] :
      ( '#skF_6'(A_101) = '#skF_6'(A_100)
      | A_100 != '#skF_7'
      | A_101 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_239])).

tff(c_128,plain,(
    ! [A_74] :
      ( k2_relat_1(A_74) != k1_xboole_0
      | k1_xboole_0 = A_74
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    ! [A_49] :
      ( k2_relat_1('#skF_6'(A_49)) != k1_xboole_0
      | '#skF_6'(A_49) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_128])).

tff(c_274,plain,(
    ! [A_100,A_101] :
      ( k2_relat_1('#skF_6'(A_100)) != k1_xboole_0
      | '#skF_6'(A_101) = k1_xboole_0
      | A_100 != '#skF_7'
      | A_101 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_141])).

tff(c_555,plain,(
    ! [A_100] :
      ( k2_relat_1('#skF_6'(A_100)) != k1_xboole_0
      | A_100 != '#skF_7' ) ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_3463,plain,(
    ! [A_233] : A_233 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_3311,c_555])).

tff(c_3477,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3463])).

tff(c_3529,plain,(
    ! [A_236] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(A_236)))
      | A_236 != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_24,plain,(
    ! [A_42,B_43,D_48] :
      ( k1_funct_1('#skF_5'(A_42,B_43),D_48) = B_43
      | ~ r2_hidden(D_48,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_210,plain,(
    ! [B_43,A_42,D_48] :
      ( r2_hidden(B_43,k2_relat_1('#skF_5'(A_42,B_43)))
      | ~ r2_hidden(D_48,k1_relat_1('#skF_5'(A_42,B_43)))
      | ~ v1_funct_1('#skF_5'(A_42,B_43))
      | ~ v1_relat_1('#skF_5'(A_42,B_43))
      | ~ r2_hidden(D_48,A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_204])).

tff(c_216,plain,(
    ! [B_43,A_42,D_48] :
      ( r2_hidden(B_43,k2_relat_1('#skF_5'(A_42,B_43)))
      | ~ r2_hidden(D_48,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_210])).

tff(c_655,plain,(
    ! [B_43,A_133,C_134] :
      ( r2_hidden(B_43,k2_relat_1('#skF_5'(A_133,B_43)))
      | ~ r2_hidden(C_134,k2_relat_1('#skF_6'(A_133))) ) ),
    inference(resolution,[status(thm)],[c_617,c_216])).

tff(c_3644,plain,(
    ! [B_239,A_240] :
      ( r2_hidden(B_239,k2_relat_1('#skF_5'(A_240,B_239)))
      | A_240 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_3529,c_655])).

tff(c_3663,plain,(
    ! [B_43,A_99,A_42] :
      ( r2_hidden(B_43,k2_relat_1('#skF_6'(A_99)))
      | A_42 != '#skF_7'
      | A_99 != '#skF_7'
      | A_42 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_3644])).

tff(c_4083,plain,(
    ! [A_42] :
      ( A_42 != '#skF_7'
      | A_42 != '#skF_7' ) ),
    inference(splitLeft,[status(thm)],[c_3663])).

tff(c_4089,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4083])).

tff(c_4090,plain,(
    ! [B_43,A_99] :
      ( r2_hidden(B_43,k2_relat_1('#skF_6'(A_99)))
      | A_99 != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_3663])).

tff(c_554,plain,(
    ! [A_49,C_118] :
      ( r2_hidden('#skF_4'('#skF_6'(A_49),k2_relat_1('#skF_6'(A_49)),C_118),A_49)
      | ~ r2_hidden(C_118,k2_relat_1('#skF_6'(A_49))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_547])).

tff(c_395,plain,(
    ! [A_107,C_108] :
      ( k1_funct_1(A_107,'#skF_4'(A_107,k2_relat_1(A_107),C_108)) = C_108
      | ~ r2_hidden(C_108,k2_relat_1(A_107))
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_420,plain,(
    ! [C_108,A_49] :
      ( k1_xboole_0 = C_108
      | ~ r2_hidden(C_108,k2_relat_1('#skF_6'(A_49)))
      | ~ v1_funct_1('#skF_6'(A_49))
      | ~ v1_relat_1('#skF_6'(A_49))
      | ~ r2_hidden('#skF_4'('#skF_6'(A_49),k2_relat_1('#skF_6'(A_49)),C_108),A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_395])).

tff(c_5055,plain,(
    ! [C_287,A_288] :
      ( k1_xboole_0 = C_287
      | ~ r2_hidden(C_287,k2_relat_1('#skF_6'(A_288)))
      | ~ r2_hidden('#skF_4'('#skF_6'(A_288),k2_relat_1('#skF_6'(A_288)),C_287),A_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_420])).

tff(c_5098,plain,(
    ! [C_289,A_290] :
      ( k1_xboole_0 = C_289
      | ~ r2_hidden(C_289,k2_relat_1('#skF_6'(A_290))) ) ),
    inference(resolution,[status(thm)],[c_554,c_5055])).

tff(c_5161,plain,(
    ! [B_43,A_99] :
      ( k1_xboole_0 = B_43
      | A_99 != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_4090,c_5098])).

tff(c_5176,plain,(
    ! [A_99] : A_99 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_5161])).

tff(c_5180,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5176])).

tff(c_5189,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_5161])).

tff(c_5181,plain,(
    ! [B_43] : k1_xboole_0 = B_43 ),
    inference(splitRight,[status(thm)],[c_5161])).

tff(c_5424,plain,(
    ! [B_1185] : B_1185 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_5189,c_5181])).

tff(c_4243,plain,(
    ! [A_263,C_264] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(A_263)))
      | ~ r2_hidden(C_264,k2_relat_1('#skF_6'(k2_relat_1('#skF_6'(A_263))))) ) ),
    inference(resolution,[status(thm)],[c_554,c_657])).

tff(c_4308,plain,(
    ! [A_265] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(A_265)))
      | k2_relat_1('#skF_6'(A_265)) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_4090,c_4243])).

tff(c_325,plain,(
    ! [A_104,A_105,B_106] :
      ( '#skF_6'(A_104) = '#skF_5'(A_105,B_106)
      | A_104 != '#skF_7'
      | A_105 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_237])).

tff(c_343,plain,(
    ! [A_104,D_48,B_106,A_105] :
      ( k1_funct_1('#skF_6'(A_104),D_48) = B_106
      | ~ r2_hidden(D_48,A_105)
      | A_104 != '#skF_7'
      | A_105 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_24])).

tff(c_4358,plain,(
    ! [A_104,B_106,A_265] :
      ( k1_funct_1('#skF_6'(A_104),k1_xboole_0) = B_106
      | A_104 != '#skF_7'
      | k2_relat_1('#skF_6'(A_265)) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_4308,c_343])).

tff(c_4455,plain,(
    ! [A_265] : k2_relat_1('#skF_6'(A_265)) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_4358])).

tff(c_5632,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5424,c_4455])).

tff(c_5650,plain,(
    ! [A_2082] :
      ( k1_funct_1('#skF_6'(A_2082),k1_xboole_0) = k1_xboole_0
      | A_2082 != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_4358])).

tff(c_5633,plain,(
    ! [A_104,B_106] :
      ( k1_funct_1('#skF_6'(A_104),k1_xboole_0) = B_106
      | A_104 != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_4358])).

tff(c_5653,plain,(
    ! [B_106,A_2082] :
      ( k1_xboole_0 = B_106
      | A_2082 != '#skF_7'
      | A_2082 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5650,c_5633])).

tff(c_6417,plain,(
    ! [A_2082] :
      ( A_2082 != '#skF_7'
      | A_2082 != '#skF_7' ) ),
    inference(splitLeft,[status(thm)],[c_5653])).

tff(c_6423,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6417])).

tff(c_6426,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_5653])).

tff(c_6424,plain,(
    ! [B_106] : k1_xboole_0 = B_106 ),
    inference(splitRight,[status(thm)],[c_5653])).

tff(c_6718,plain,(
    ! [B_4217] : B_4217 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_6426,c_6424])).

tff(c_4298,plain,(
    ! [A_263] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(A_263)))
      | k2_relat_1('#skF_6'(A_263)) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_4090,c_4243])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6069,plain,(
    ! [A_2082] :
      ( k1_funct_1('#skF_6'(A_2082),k1_xboole_0) = '#skF_7'
      | A_2082 != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_4358])).

tff(c_6072,plain,(
    ! [A_2082] :
      ( k1_xboole_0 = '#skF_7'
      | ~ r2_hidden(k1_xboole_0,A_2082)
      | A_2082 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6069,c_32])).

tff(c_6222,plain,(
    ! [A_3188] :
      ( ~ r2_hidden(k1_xboole_0,A_3188)
      | A_3188 != '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_6072])).

tff(c_6259,plain,(
    ! [A_263] : k2_relat_1('#skF_6'(A_263)) != '#skF_7' ),
    inference(resolution,[status(thm)],[c_4298,c_6222])).

tff(c_6975,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_6718,c_6259])).

tff(c_6978,plain,(
    ! [A_5226] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(A_5226)))
      | k1_xboole_0 != A_5226 ) ),
    inference(splitRight,[status(thm)],[c_674])).

tff(c_7013,plain,(
    ! [B_5227,A_5228] :
      ( r2_hidden(B_5227,k2_relat_1('#skF_5'(A_5228,B_5227)))
      | k1_xboole_0 != A_5228 ) ),
    inference(resolution,[status(thm)],[c_6978,c_655])).

tff(c_7035,plain,(
    ! [B_43,A_42] :
      ( r2_hidden(B_43,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_42
      | k1_xboole_0 != A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_7013])).

tff(c_7252,plain,(
    ! [A_42] :
      ( k1_xboole_0 != A_42
      | k1_xboole_0 != A_42 ) ),
    inference(splitLeft,[status(thm)],[c_7035])).

tff(c_7258,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7252])).

tff(c_7259,plain,(
    ! [B_43] : r2_hidden(B_43,k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_7035])).

tff(c_8105,plain,(
    ! [C_5266,A_5267] :
      ( k1_xboole_0 = C_5266
      | ~ r2_hidden(C_5266,k2_relat_1('#skF_6'(A_5267)))
      | ~ r2_hidden('#skF_4'('#skF_6'(A_5267),k2_relat_1('#skF_6'(A_5267)),C_5266),A_5267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_420])).

tff(c_8139,plain,(
    ! [C_5268,A_5269] :
      ( k1_xboole_0 = C_5268
      | ~ r2_hidden(C_5268,k2_relat_1('#skF_6'(A_5269))) ) ),
    inference(resolution,[status(thm)],[c_554,c_8105])).

tff(c_8197,plain,(
    ! [C_5268,A_49] :
      ( k1_xboole_0 = C_5268
      | ~ r2_hidden(C_5268,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_8139])).

tff(c_8226,plain,(
    ! [C_5268,A_49] :
      ( k1_xboole_0 = C_5268
      | k1_xboole_0 != A_49 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7259,c_8197])).

tff(c_8227,plain,(
    ! [A_49] : k1_xboole_0 != A_49 ),
    inference(splitLeft,[status(thm)],[c_8226])).

tff(c_8239,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8227])).

tff(c_8247,plain,(
    ! [C_5270] : k1_xboole_0 = C_5270 ),
    inference(splitRight,[status(thm)],[c_8226])).

tff(c_7004,plain,(
    ! [A_49] :
      ( r2_hidden(k1_xboole_0,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_49
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_6978])).

tff(c_7041,plain,(
    ! [A_49] :
      ( k1_xboole_0 != A_49
      | k1_xboole_0 != A_49 ) ),
    inference(splitLeft,[status(thm)],[c_7004])).

tff(c_7106,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7041])).

tff(c_7107,plain,(
    r2_hidden(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_7004])).

tff(c_7122,plain,(
    r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0)))) ),
    inference(resolution,[status(thm)],[c_7107,c_218])).

tff(c_7156,plain,(
    r2_hidden(k1_xboole_0,k2_relat_1('#skF_6'(k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0)))))) ),
    inference(resolution,[status(thm)],[c_7122,c_218])).

tff(c_186,plain,(
    ! [A_81,B_82,D_83] :
      ( k1_funct_1('#skF_5'(A_81,B_82),D_83) = B_82
      | ~ r2_hidden(D_83,A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_195,plain,(
    ! [D_83,B_43,A_42] :
      ( k1_funct_1(k1_xboole_0,D_83) = B_43
      | ~ r2_hidden(D_83,A_42)
      | k1_xboole_0 != A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_186])).

tff(c_7322,plain,(
    ! [B_43] :
      ( k1_funct_1(k1_xboole_0,k1_xboole_0) = B_43
      | k2_relat_1('#skF_6'(k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0))))) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7156,c_195])).

tff(c_7954,plain,(
    k2_relat_1('#skF_6'(k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0))))) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7322])).

tff(c_8647,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_8247,c_7954])).

tff(c_8660,plain,(
    k1_funct_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7322])).

tff(c_8648,plain,(
    ! [B_43] : k1_funct_1(k1_xboole_0,k1_xboole_0) = B_43 ),
    inference(splitRight,[status(thm)],[c_7322])).

tff(c_9160,plain,(
    ! [B_7448] : k1_xboole_0 = B_7448 ),
    inference(superposition,[status(thm),theory(equality)],[c_8660,c_8648])).

tff(c_7154,plain,(
    ! [B_43] :
      ( k1_funct_1(k1_xboole_0,k1_xboole_0) = B_43
      | k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0))) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7122,c_195])).

tff(c_7376,plain,(
    k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0))) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7154])).

tff(c_9550,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_9160,c_7376])).

tff(c_9569,plain,(
    k1_funct_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7154])).

tff(c_9551,plain,(
    ! [B_43] : k1_funct_1(k1_xboole_0,k1_xboole_0) = B_43 ),
    inference(splitRight,[status(thm)],[c_7154])).

tff(c_9915,plain,(
    ! [B_9357] : k1_xboole_0 = B_9357 ),
    inference(superposition,[status(thm),theory(equality)],[c_9569,c_9551])).

tff(c_7120,plain,(
    ! [B_43] :
      ( k1_funct_1(k1_xboole_0,k1_xboole_0) = B_43
      | k2_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7107,c_195])).

tff(c_7159,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7120])).

tff(c_10111,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_9915,c_7159])).

tff(c_10168,plain,(
    k1_funct_1(k1_xboole_0,k1_xboole_0) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7120])).

tff(c_10112,plain,(
    ! [B_43] : k1_funct_1(k1_xboole_0,k1_xboole_0) = B_43 ),
    inference(splitRight,[status(thm)],[c_7120])).

tff(c_10603,plain,(
    ! [B_11552] : B_11552 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_10168,c_10112])).

tff(c_10720,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_10603,c_40])).

tff(c_10723,plain,(
    ! [A_12241] :
      ( '#skF_6'(A_12241) = k1_xboole_0
      | A_12241 != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_10747,plain,(
    ! [A_12241] :
      ( k1_relat_1(k1_xboole_0) = A_12241
      | A_12241 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10723,c_34])).

tff(c_10772,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_10747])).

tff(c_10789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10772,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:00:25 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.66/2.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/2.64  
% 7.66/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/2.64  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6
% 7.66/2.64  
% 7.66/2.64  %Foreground sorts:
% 7.66/2.64  
% 7.66/2.64  
% 7.66/2.64  %Background operators:
% 7.66/2.64  
% 7.66/2.64  
% 7.66/2.64  %Foreground operators:
% 7.66/2.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.66/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.66/2.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.66/2.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.66/2.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.66/2.64  tff('#skF_7', type, '#skF_7': $i).
% 7.66/2.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.66/2.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.66/2.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.66/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.66/2.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.66/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.66/2.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.66/2.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.66/2.64  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.66/2.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.66/2.64  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.66/2.64  
% 7.66/2.67  tff(f_72, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 7.66/2.67  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.66/2.67  tff(f_60, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 7.66/2.67  tff(f_91, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 7.66/2.67  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 7.66/2.67  tff(c_34, plain, (![A_49]: (k1_relat_1('#skF_6'(A_49))=A_49)), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.66/2.67  tff(c_38, plain, (![A_49]: (v1_relat_1('#skF_6'(A_49)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.66/2.67  tff(c_65, plain, (![A_70]: (k1_relat_1(A_70)!=k1_xboole_0 | k1_xboole_0=A_70 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.66/2.67  tff(c_71, plain, (![A_49]: (k1_relat_1('#skF_6'(A_49))!=k1_xboole_0 | '#skF_6'(A_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_65])).
% 7.66/2.67  tff(c_77, plain, (![A_71]: (k1_xboole_0!=A_71 | '#skF_6'(A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_71])).
% 7.66/2.67  tff(c_142, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_77, c_34])).
% 7.66/2.67  tff(c_26, plain, (![A_42, B_43]: (k1_relat_1('#skF_5'(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.66/2.67  tff(c_30, plain, (![A_42, B_43]: (v1_relat_1('#skF_5'(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.66/2.67  tff(c_68, plain, (![A_42, B_43]: (k1_relat_1('#skF_5'(A_42, B_43))!=k1_xboole_0 | '#skF_5'(A_42, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_65])).
% 7.66/2.67  tff(c_73, plain, (![A_42, B_43]: (k1_xboole_0!=A_42 | '#skF_5'(A_42, B_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 7.66/2.67  tff(c_28, plain, (![A_42, B_43]: (v1_funct_1('#skF_5'(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.66/2.67  tff(c_36, plain, (![A_49]: (v1_funct_1('#skF_6'(A_49)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.66/2.67  tff(c_93, plain, (![C_72, B_73]: (C_72=B_73 | k1_relat_1(C_72)!='#skF_7' | k1_relat_1(B_73)!='#skF_7' | ~v1_funct_1(C_72) | ~v1_relat_1(C_72) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.66/2.67  tff(c_97, plain, (![B_73, A_49]: (B_73='#skF_6'(A_49) | k1_relat_1('#skF_6'(A_49))!='#skF_7' | k1_relat_1(B_73)!='#skF_7' | ~v1_funct_1('#skF_6'(A_49)) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_38, c_93])).
% 7.66/2.67  tff(c_233, plain, (![B_98, A_99]: (B_98='#skF_6'(A_99) | A_99!='#skF_7' | k1_relat_1(B_98)!='#skF_7' | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_97])).
% 7.66/2.67  tff(c_237, plain, (![A_99, A_42, B_43]: ('#skF_6'(A_99)='#skF_5'(A_42, B_43) | A_99!='#skF_7' | k1_relat_1('#skF_5'(A_42, B_43))!='#skF_7' | ~v1_funct_1('#skF_5'(A_42, B_43)))), inference(resolution, [status(thm)], [c_30, c_233])).
% 7.66/2.67  tff(c_245, plain, (![A_99, A_42, B_43]: ('#skF_6'(A_99)='#skF_5'(A_42, B_43) | A_99!='#skF_7' | A_42!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_237])).
% 7.66/2.67  tff(c_680, plain, (![A_137, B_138]: (r2_hidden('#skF_2'(A_137, B_138), k1_relat_1(A_137)) | r2_hidden('#skF_3'(A_137, B_138), B_138) | k2_relat_1(A_137)=B_138 | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.66/2.67  tff(c_709, plain, (![A_49, B_138]: (r2_hidden('#skF_2'('#skF_6'(A_49), B_138), A_49) | r2_hidden('#skF_3'('#skF_6'(A_49), B_138), B_138) | k2_relat_1('#skF_6'(A_49))=B_138 | ~v1_funct_1('#skF_6'(A_49)) | ~v1_relat_1('#skF_6'(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_680])).
% 7.66/2.67  tff(c_2611, plain, (![A_228, B_229]: (r2_hidden('#skF_2'('#skF_6'(A_228), B_229), A_228) | r2_hidden('#skF_3'('#skF_6'(A_228), B_229), B_229) | k2_relat_1('#skF_6'(A_228))=B_229)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_709])).
% 7.66/2.67  tff(c_85, plain, (![A_71]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_71)), inference(superposition, [status(thm), theory('equality')], [c_77, c_38])).
% 7.66/2.67  tff(c_104, plain, (![A_71]: (k1_xboole_0!=A_71)), inference(splitLeft, [status(thm)], [c_85])).
% 7.66/2.67  tff(c_110, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_104])).
% 7.66/2.67  tff(c_111, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_85])).
% 7.66/2.67  tff(c_87, plain, (![A_71]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_71)), inference(superposition, [status(thm), theory('equality')], [c_77, c_36])).
% 7.66/2.67  tff(c_120, plain, (![A_71]: (k1_xboole_0!=A_71)), inference(splitLeft, [status(thm)], [c_87])).
% 7.66/2.67  tff(c_126, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_120])).
% 7.66/2.67  tff(c_127, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_87])).
% 7.66/2.67  tff(c_6, plain, (![A_2, D_41]: (r2_hidden(k1_funct_1(A_2, D_41), k2_relat_1(A_2)) | ~r2_hidden(D_41, k1_relat_1(A_2)) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.66/2.67  tff(c_75, plain, (![A_49]: (k1_xboole_0!=A_49 | '#skF_6'(A_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_71])).
% 7.66/2.67  tff(c_535, plain, (![A_117, C_118]: (r2_hidden('#skF_4'(A_117, k2_relat_1(A_117), C_118), k1_relat_1(A_117)) | ~r2_hidden(C_118, k2_relat_1(A_117)) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.66/2.67  tff(c_547, plain, (![A_49, C_118]: (r2_hidden('#skF_4'('#skF_6'(A_49), k2_relat_1('#skF_6'(A_49)), C_118), A_49) | ~r2_hidden(C_118, k2_relat_1('#skF_6'(A_49))) | ~v1_funct_1('#skF_6'(A_49)) | ~v1_relat_1('#skF_6'(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_535])).
% 7.66/2.67  tff(c_617, plain, (![A_133, C_134]: (r2_hidden('#skF_4'('#skF_6'(A_133), k2_relat_1('#skF_6'(A_133)), C_134), A_133) | ~r2_hidden(C_134, k2_relat_1('#skF_6'(A_133))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_547])).
% 7.66/2.67  tff(c_32, plain, (![A_49, C_54]: (k1_funct_1('#skF_6'(A_49), C_54)=k1_xboole_0 | ~r2_hidden(C_54, A_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.66/2.67  tff(c_204, plain, (![A_88, D_89]: (r2_hidden(k1_funct_1(A_88, D_89), k2_relat_1(A_88)) | ~r2_hidden(D_89, k1_relat_1(A_88)) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.66/2.67  tff(c_213, plain, (![A_49, C_54]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(A_49))) | ~r2_hidden(C_54, k1_relat_1('#skF_6'(A_49))) | ~v1_funct_1('#skF_6'(A_49)) | ~v1_relat_1('#skF_6'(A_49)) | ~r2_hidden(C_54, A_49))), inference(superposition, [status(thm), theory('equality')], [c_32, c_204])).
% 7.66/2.67  tff(c_218, plain, (![A_49, C_54]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(A_49))) | ~r2_hidden(C_54, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_213])).
% 7.66/2.67  tff(c_657, plain, (![A_135, C_136]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(A_135))) | ~r2_hidden(C_136, k2_relat_1('#skF_6'(A_135))))), inference(resolution, [status(thm)], [c_617, c_218])).
% 7.66/2.67  tff(c_674, plain, (![A_49, C_136]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(A_49))) | ~r2_hidden(C_136, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_75, c_657])).
% 7.66/2.67  tff(c_753, plain, (![C_142]: (~r2_hidden(C_142, k2_relat_1(k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_674])).
% 7.66/2.67  tff(c_769, plain, (![D_41]: (~r2_hidden(D_41, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_753])).
% 7.66/2.67  tff(c_775, plain, (![D_41]: (~r2_hidden(D_41, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_127, c_142, c_769])).
% 7.66/2.67  tff(c_2947, plain, (![A_230]: (r2_hidden('#skF_2'('#skF_6'(A_230), k1_xboole_0), A_230) | k2_relat_1('#skF_6'(A_230))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2611, c_775])).
% 7.66/2.67  tff(c_239, plain, (![A_99, A_49]: ('#skF_6'(A_99)='#skF_6'(A_49) | A_99!='#skF_7' | k1_relat_1('#skF_6'(A_49))!='#skF_7' | ~v1_funct_1('#skF_6'(A_49)))), inference(resolution, [status(thm)], [c_38, c_233])).
% 7.66/2.67  tff(c_248, plain, (![A_99, A_49]: ('#skF_6'(A_99)='#skF_6'(A_49) | A_99!='#skF_7' | A_49!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_239])).
% 7.66/2.67  tff(c_667, plain, (![A_49, C_136, A_99]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(A_49))) | ~r2_hidden(C_136, k2_relat_1('#skF_6'(A_99))) | A_99!='#skF_7' | A_49!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_248, c_657])).
% 7.66/2.67  tff(c_827, plain, (![C_145, A_146]: (~r2_hidden(C_145, k2_relat_1('#skF_6'(A_146))) | A_146!='#skF_7')), inference(splitLeft, [status(thm)], [c_667])).
% 7.66/2.67  tff(c_852, plain, (![A_146, D_41]: (A_146!='#skF_7' | ~r2_hidden(D_41, k1_relat_1('#skF_6'(A_146))) | ~v1_funct_1('#skF_6'(A_146)) | ~v1_relat_1('#skF_6'(A_146)))), inference(resolution, [status(thm)], [c_6, c_827])).
% 7.66/2.67  tff(c_861, plain, (![A_146, D_41]: (A_146!='#skF_7' | ~r2_hidden(D_41, A_146))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_852])).
% 7.66/2.67  tff(c_3311, plain, (![A_233]: (A_233!='#skF_7' | k2_relat_1('#skF_6'(A_233))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2947, c_861])).
% 7.66/2.67  tff(c_250, plain, (![A_101, A_100]: ('#skF_6'(A_101)='#skF_6'(A_100) | A_100!='#skF_7' | A_101!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_239])).
% 7.66/2.67  tff(c_128, plain, (![A_74]: (k2_relat_1(A_74)!=k1_xboole_0 | k1_xboole_0=A_74 | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.66/2.67  tff(c_141, plain, (![A_49]: (k2_relat_1('#skF_6'(A_49))!=k1_xboole_0 | '#skF_6'(A_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_128])).
% 7.66/2.67  tff(c_274, plain, (![A_100, A_101]: (k2_relat_1('#skF_6'(A_100))!=k1_xboole_0 | '#skF_6'(A_101)=k1_xboole_0 | A_100!='#skF_7' | A_101!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_250, c_141])).
% 7.66/2.67  tff(c_555, plain, (![A_100]: (k2_relat_1('#skF_6'(A_100))!=k1_xboole_0 | A_100!='#skF_7')), inference(splitLeft, [status(thm)], [c_274])).
% 7.66/2.67  tff(c_3463, plain, (![A_233]: (A_233!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3311, c_555])).
% 7.66/2.67  tff(c_3477, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_3463])).
% 7.66/2.67  tff(c_3529, plain, (![A_236]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(A_236))) | A_236!='#skF_7')), inference(splitRight, [status(thm)], [c_667])).
% 7.66/2.67  tff(c_24, plain, (![A_42, B_43, D_48]: (k1_funct_1('#skF_5'(A_42, B_43), D_48)=B_43 | ~r2_hidden(D_48, A_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.66/2.67  tff(c_210, plain, (![B_43, A_42, D_48]: (r2_hidden(B_43, k2_relat_1('#skF_5'(A_42, B_43))) | ~r2_hidden(D_48, k1_relat_1('#skF_5'(A_42, B_43))) | ~v1_funct_1('#skF_5'(A_42, B_43)) | ~v1_relat_1('#skF_5'(A_42, B_43)) | ~r2_hidden(D_48, A_42))), inference(superposition, [status(thm), theory('equality')], [c_24, c_204])).
% 7.66/2.67  tff(c_216, plain, (![B_43, A_42, D_48]: (r2_hidden(B_43, k2_relat_1('#skF_5'(A_42, B_43))) | ~r2_hidden(D_48, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_210])).
% 7.66/2.67  tff(c_655, plain, (![B_43, A_133, C_134]: (r2_hidden(B_43, k2_relat_1('#skF_5'(A_133, B_43))) | ~r2_hidden(C_134, k2_relat_1('#skF_6'(A_133))))), inference(resolution, [status(thm)], [c_617, c_216])).
% 7.66/2.67  tff(c_3644, plain, (![B_239, A_240]: (r2_hidden(B_239, k2_relat_1('#skF_5'(A_240, B_239))) | A_240!='#skF_7')), inference(resolution, [status(thm)], [c_3529, c_655])).
% 7.66/2.67  tff(c_3663, plain, (![B_43, A_99, A_42]: (r2_hidden(B_43, k2_relat_1('#skF_6'(A_99))) | A_42!='#skF_7' | A_99!='#skF_7' | A_42!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_245, c_3644])).
% 7.66/2.67  tff(c_4083, plain, (![A_42]: (A_42!='#skF_7' | A_42!='#skF_7')), inference(splitLeft, [status(thm)], [c_3663])).
% 7.66/2.67  tff(c_4089, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_4083])).
% 7.66/2.67  tff(c_4090, plain, (![B_43, A_99]: (r2_hidden(B_43, k2_relat_1('#skF_6'(A_99))) | A_99!='#skF_7')), inference(splitRight, [status(thm)], [c_3663])).
% 7.66/2.67  tff(c_554, plain, (![A_49, C_118]: (r2_hidden('#skF_4'('#skF_6'(A_49), k2_relat_1('#skF_6'(A_49)), C_118), A_49) | ~r2_hidden(C_118, k2_relat_1('#skF_6'(A_49))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_547])).
% 7.66/2.67  tff(c_395, plain, (![A_107, C_108]: (k1_funct_1(A_107, '#skF_4'(A_107, k2_relat_1(A_107), C_108))=C_108 | ~r2_hidden(C_108, k2_relat_1(A_107)) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.66/2.67  tff(c_420, plain, (![C_108, A_49]: (k1_xboole_0=C_108 | ~r2_hidden(C_108, k2_relat_1('#skF_6'(A_49))) | ~v1_funct_1('#skF_6'(A_49)) | ~v1_relat_1('#skF_6'(A_49)) | ~r2_hidden('#skF_4'('#skF_6'(A_49), k2_relat_1('#skF_6'(A_49)), C_108), A_49))), inference(superposition, [status(thm), theory('equality')], [c_32, c_395])).
% 7.66/2.67  tff(c_5055, plain, (![C_287, A_288]: (k1_xboole_0=C_287 | ~r2_hidden(C_287, k2_relat_1('#skF_6'(A_288))) | ~r2_hidden('#skF_4'('#skF_6'(A_288), k2_relat_1('#skF_6'(A_288)), C_287), A_288))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_420])).
% 7.66/2.67  tff(c_5098, plain, (![C_289, A_290]: (k1_xboole_0=C_289 | ~r2_hidden(C_289, k2_relat_1('#skF_6'(A_290))))), inference(resolution, [status(thm)], [c_554, c_5055])).
% 7.66/2.67  tff(c_5161, plain, (![B_43, A_99]: (k1_xboole_0=B_43 | A_99!='#skF_7')), inference(resolution, [status(thm)], [c_4090, c_5098])).
% 7.66/2.67  tff(c_5176, plain, (![A_99]: (A_99!='#skF_7')), inference(splitLeft, [status(thm)], [c_5161])).
% 7.66/2.67  tff(c_5180, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_5176])).
% 7.66/2.67  tff(c_5189, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_5161])).
% 7.66/2.67  tff(c_5181, plain, (![B_43]: (k1_xboole_0=B_43)), inference(splitRight, [status(thm)], [c_5161])).
% 7.66/2.67  tff(c_5424, plain, (![B_1185]: (B_1185='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5189, c_5181])).
% 7.66/2.67  tff(c_4243, plain, (![A_263, C_264]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(A_263))) | ~r2_hidden(C_264, k2_relat_1('#skF_6'(k2_relat_1('#skF_6'(A_263))))))), inference(resolution, [status(thm)], [c_554, c_657])).
% 7.66/2.67  tff(c_4308, plain, (![A_265]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(A_265))) | k2_relat_1('#skF_6'(A_265))!='#skF_7')), inference(resolution, [status(thm)], [c_4090, c_4243])).
% 7.66/2.67  tff(c_325, plain, (![A_104, A_105, B_106]: ('#skF_6'(A_104)='#skF_5'(A_105, B_106) | A_104!='#skF_7' | A_105!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_237])).
% 7.66/2.67  tff(c_343, plain, (![A_104, D_48, B_106, A_105]: (k1_funct_1('#skF_6'(A_104), D_48)=B_106 | ~r2_hidden(D_48, A_105) | A_104!='#skF_7' | A_105!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_325, c_24])).
% 7.66/2.67  tff(c_4358, plain, (![A_104, B_106, A_265]: (k1_funct_1('#skF_6'(A_104), k1_xboole_0)=B_106 | A_104!='#skF_7' | k2_relat_1('#skF_6'(A_265))!='#skF_7')), inference(resolution, [status(thm)], [c_4308, c_343])).
% 7.66/2.67  tff(c_4455, plain, (![A_265]: (k2_relat_1('#skF_6'(A_265))!='#skF_7')), inference(splitLeft, [status(thm)], [c_4358])).
% 7.66/2.67  tff(c_5632, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5424, c_4455])).
% 7.66/2.67  tff(c_5650, plain, (![A_2082]: (k1_funct_1('#skF_6'(A_2082), k1_xboole_0)=k1_xboole_0 | A_2082!='#skF_7')), inference(splitRight, [status(thm)], [c_4358])).
% 7.66/2.67  tff(c_5633, plain, (![A_104, B_106]: (k1_funct_1('#skF_6'(A_104), k1_xboole_0)=B_106 | A_104!='#skF_7')), inference(splitRight, [status(thm)], [c_4358])).
% 7.66/2.67  tff(c_5653, plain, (![B_106, A_2082]: (k1_xboole_0=B_106 | A_2082!='#skF_7' | A_2082!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5650, c_5633])).
% 7.66/2.67  tff(c_6417, plain, (![A_2082]: (A_2082!='#skF_7' | A_2082!='#skF_7')), inference(splitLeft, [status(thm)], [c_5653])).
% 7.66/2.67  tff(c_6423, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_6417])).
% 7.66/2.67  tff(c_6426, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_5653])).
% 7.66/2.67  tff(c_6424, plain, (![B_106]: (k1_xboole_0=B_106)), inference(splitRight, [status(thm)], [c_5653])).
% 7.66/2.67  tff(c_6718, plain, (![B_4217]: (B_4217='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6426, c_6424])).
% 7.66/2.67  tff(c_4298, plain, (![A_263]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(A_263))) | k2_relat_1('#skF_6'(A_263))!='#skF_7')), inference(resolution, [status(thm)], [c_4090, c_4243])).
% 7.66/2.67  tff(c_40, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.66/2.67  tff(c_6069, plain, (![A_2082]: (k1_funct_1('#skF_6'(A_2082), k1_xboole_0)='#skF_7' | A_2082!='#skF_7')), inference(splitRight, [status(thm)], [c_4358])).
% 7.66/2.67  tff(c_6072, plain, (![A_2082]: (k1_xboole_0='#skF_7' | ~r2_hidden(k1_xboole_0, A_2082) | A_2082!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6069, c_32])).
% 7.66/2.67  tff(c_6222, plain, (![A_3188]: (~r2_hidden(k1_xboole_0, A_3188) | A_3188!='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_40, c_6072])).
% 7.66/2.67  tff(c_6259, plain, (![A_263]: (k2_relat_1('#skF_6'(A_263))!='#skF_7')), inference(resolution, [status(thm)], [c_4298, c_6222])).
% 7.66/2.67  tff(c_6975, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_6718, c_6259])).
% 7.66/2.67  tff(c_6978, plain, (![A_5226]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(A_5226))) | k1_xboole_0!=A_5226)), inference(splitRight, [status(thm)], [c_674])).
% 7.66/2.67  tff(c_7013, plain, (![B_5227, A_5228]: (r2_hidden(B_5227, k2_relat_1('#skF_5'(A_5228, B_5227))) | k1_xboole_0!=A_5228)), inference(resolution, [status(thm)], [c_6978, c_655])).
% 7.66/2.67  tff(c_7035, plain, (![B_43, A_42]: (r2_hidden(B_43, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_42 | k1_xboole_0!=A_42)), inference(superposition, [status(thm), theory('equality')], [c_73, c_7013])).
% 7.66/2.67  tff(c_7252, plain, (![A_42]: (k1_xboole_0!=A_42 | k1_xboole_0!=A_42)), inference(splitLeft, [status(thm)], [c_7035])).
% 7.66/2.67  tff(c_7258, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_7252])).
% 7.66/2.67  tff(c_7259, plain, (![B_43]: (r2_hidden(B_43, k2_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_7035])).
% 7.66/2.67  tff(c_8105, plain, (![C_5266, A_5267]: (k1_xboole_0=C_5266 | ~r2_hidden(C_5266, k2_relat_1('#skF_6'(A_5267))) | ~r2_hidden('#skF_4'('#skF_6'(A_5267), k2_relat_1('#skF_6'(A_5267)), C_5266), A_5267))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_420])).
% 7.66/2.67  tff(c_8139, plain, (![C_5268, A_5269]: (k1_xboole_0=C_5268 | ~r2_hidden(C_5268, k2_relat_1('#skF_6'(A_5269))))), inference(resolution, [status(thm)], [c_554, c_8105])).
% 7.66/2.67  tff(c_8197, plain, (![C_5268, A_49]: (k1_xboole_0=C_5268 | ~r2_hidden(C_5268, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_75, c_8139])).
% 7.66/2.67  tff(c_8226, plain, (![C_5268, A_49]: (k1_xboole_0=C_5268 | k1_xboole_0!=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_7259, c_8197])).
% 7.66/2.67  tff(c_8227, plain, (![A_49]: (k1_xboole_0!=A_49)), inference(splitLeft, [status(thm)], [c_8226])).
% 7.66/2.67  tff(c_8239, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_8227])).
% 7.66/2.67  tff(c_8247, plain, (![C_5270]: (k1_xboole_0=C_5270)), inference(splitRight, [status(thm)], [c_8226])).
% 7.66/2.67  tff(c_7004, plain, (![A_49]: (r2_hidden(k1_xboole_0, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_49 | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_75, c_6978])).
% 7.66/2.67  tff(c_7041, plain, (![A_49]: (k1_xboole_0!=A_49 | k1_xboole_0!=A_49)), inference(splitLeft, [status(thm)], [c_7004])).
% 7.66/2.67  tff(c_7106, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_7041])).
% 7.66/2.67  tff(c_7107, plain, (r2_hidden(k1_xboole_0, k2_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_7004])).
% 7.66/2.67  tff(c_7122, plain, (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0))))), inference(resolution, [status(thm)], [c_7107, c_218])).
% 7.66/2.67  tff(c_7156, plain, (r2_hidden(k1_xboole_0, k2_relat_1('#skF_6'(k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0))))))), inference(resolution, [status(thm)], [c_7122, c_218])).
% 7.66/2.67  tff(c_186, plain, (![A_81, B_82, D_83]: (k1_funct_1('#skF_5'(A_81, B_82), D_83)=B_82 | ~r2_hidden(D_83, A_81))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.66/2.67  tff(c_195, plain, (![D_83, B_43, A_42]: (k1_funct_1(k1_xboole_0, D_83)=B_43 | ~r2_hidden(D_83, A_42) | k1_xboole_0!=A_42)), inference(superposition, [status(thm), theory('equality')], [c_73, c_186])).
% 7.66/2.67  tff(c_7322, plain, (![B_43]: (k1_funct_1(k1_xboole_0, k1_xboole_0)=B_43 | k2_relat_1('#skF_6'(k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0)))))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7156, c_195])).
% 7.66/2.67  tff(c_7954, plain, (k2_relat_1('#skF_6'(k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0)))))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7322])).
% 7.66/2.67  tff(c_8647, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_8247, c_7954])).
% 7.66/2.67  tff(c_8660, plain, (k1_funct_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_7322])).
% 7.66/2.67  tff(c_8648, plain, (![B_43]: (k1_funct_1(k1_xboole_0, k1_xboole_0)=B_43)), inference(splitRight, [status(thm)], [c_7322])).
% 7.66/2.67  tff(c_9160, plain, (![B_7448]: (k1_xboole_0=B_7448)), inference(superposition, [status(thm), theory('equality')], [c_8660, c_8648])).
% 7.66/2.67  tff(c_7154, plain, (![B_43]: (k1_funct_1(k1_xboole_0, k1_xboole_0)=B_43 | k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0)))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7122, c_195])).
% 7.66/2.67  tff(c_7376, plain, (k2_relat_1('#skF_6'(k2_relat_1(k1_xboole_0)))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7154])).
% 7.66/2.67  tff(c_9550, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_9160, c_7376])).
% 7.66/2.67  tff(c_9569, plain, (k1_funct_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_7154])).
% 7.66/2.67  tff(c_9551, plain, (![B_43]: (k1_funct_1(k1_xboole_0, k1_xboole_0)=B_43)), inference(splitRight, [status(thm)], [c_7154])).
% 7.66/2.67  tff(c_9915, plain, (![B_9357]: (k1_xboole_0=B_9357)), inference(superposition, [status(thm), theory('equality')], [c_9569, c_9551])).
% 7.66/2.67  tff(c_7120, plain, (![B_43]: (k1_funct_1(k1_xboole_0, k1_xboole_0)=B_43 | k2_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7107, c_195])).
% 7.66/2.67  tff(c_7159, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7120])).
% 7.66/2.67  tff(c_10111, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_9915, c_7159])).
% 7.66/2.67  tff(c_10168, plain, (k1_funct_1(k1_xboole_0, k1_xboole_0)='#skF_7'), inference(splitRight, [status(thm)], [c_7120])).
% 7.66/2.67  tff(c_10112, plain, (![B_43]: (k1_funct_1(k1_xboole_0, k1_xboole_0)=B_43)), inference(splitRight, [status(thm)], [c_7120])).
% 7.66/2.67  tff(c_10603, plain, (![B_11552]: (B_11552='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10168, c_10112])).
% 7.66/2.67  tff(c_10720, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_10603, c_40])).
% 7.66/2.67  tff(c_10723, plain, (![A_12241]: ('#skF_6'(A_12241)=k1_xboole_0 | A_12241!='#skF_7')), inference(splitRight, [status(thm)], [c_274])).
% 7.66/2.67  tff(c_10747, plain, (![A_12241]: (k1_relat_1(k1_xboole_0)=A_12241 | A_12241!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10723, c_34])).
% 7.66/2.67  tff(c_10772, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_10747])).
% 7.66/2.67  tff(c_10789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10772, c_40])).
% 7.66/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/2.67  
% 7.66/2.67  Inference rules
% 7.66/2.67  ----------------------
% 7.66/2.67  #Ref     : 16
% 7.66/2.67  #Sup     : 3251
% 7.66/2.67  #Fact    : 0
% 7.66/2.67  #Define  : 0
% 7.66/2.67  #Split   : 27
% 7.66/2.67  #Chain   : 0
% 7.66/2.67  #Close   : 0
% 7.66/2.67  
% 7.66/2.67  Ordering : KBO
% 7.66/2.67  
% 7.66/2.67  Simplification rules
% 7.66/2.67  ----------------------
% 7.66/2.67  #Subsume      : 1136
% 7.66/2.67  #Demod        : 780
% 7.66/2.67  #Tautology    : 203
% 7.66/2.67  #SimpNegUnit  : 82
% 7.66/2.67  #BackRed      : 33
% 7.66/2.67  
% 7.66/2.67  #Partial instantiations: 3074
% 7.66/2.67  #Strategies tried      : 1
% 7.66/2.67  
% 7.66/2.67  Timing (in seconds)
% 7.66/2.67  ----------------------
% 7.66/2.67  Preprocessing        : 0.32
% 7.66/2.67  Parsing              : 0.17
% 7.66/2.67  CNF conversion       : 0.03
% 7.66/2.67  Main loop            : 1.50
% 7.66/2.67  Inferencing          : 0.50
% 7.66/2.67  Reduction            : 0.50
% 7.66/2.68  Demodulation         : 0.33
% 7.66/2.68  BG Simplification    : 0.06
% 7.66/2.68  Subsumption          : 0.34
% 7.66/2.68  Abstraction          : 0.08
% 7.66/2.68  MUC search           : 0.00
% 7.66/2.68  Cooper               : 0.00
% 7.66/2.68  Total                : 1.88
% 7.66/2.68  Index Insertion      : 0.00
% 7.66/2.68  Index Deletion       : 0.00
% 7.66/2.68  Index Matching       : 0.00
% 7.66/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
