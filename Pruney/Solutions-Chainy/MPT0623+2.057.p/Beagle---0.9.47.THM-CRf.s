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
% DateTime   : Thu Dec  3 10:03:13 EST 2020

% Result     : Theorem 13.69s
% Output     : CNFRefutation 13.69s
% Verified   : 
% Statistics : Number of formulae       :  271 (3213 expanded)
%              Number of leaves         :   24 (1104 expanded)
%              Depth                    :   19
%              Number of atoms          :  584 (9713 expanded)
%              Number of equality atoms :  204 (4017 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
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
    ! [A_48,B_49] : k1_relat_1('#skF_6'(A_48,B_49)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [A_48,B_49] : v1_relat_1('#skF_6'(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_56,plain,(
    ! [A_64] :
      ( k1_relat_1(A_64) != k1_xboole_0
      | k1_xboole_0 = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [A_48,B_49] :
      ( k1_relat_1('#skF_6'(A_48,B_49)) != k1_xboole_0
      | '#skF_6'(A_48,B_49) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_61,plain,(
    ! [A_48,B_49] :
      ( k1_xboole_0 != A_48
      | '#skF_6'(A_48,B_49) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_59])).

tff(c_36,plain,(
    ! [A_48,B_49] : v1_funct_1('#skF_6'(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_235,plain,(
    ! [A_102,C_103] :
      ( r2_hidden('#skF_5'(A_102,k2_relat_1(A_102),C_103),k1_relat_1(A_102))
      | ~ r2_hidden(C_103,k2_relat_1(A_102))
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_48,B_49,D_54] :
      ( k1_funct_1('#skF_6'(A_48,B_49),D_54) = B_49
      | ~ r2_hidden(D_54,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_151,plain,(
    ! [A_87,D_88] :
      ( r2_hidden(k1_funct_1(A_87,D_88),k2_relat_1(A_87))
      | ~ r2_hidden(D_88,k1_relat_1(A_87))
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    ! [B_49,A_48,D_54] :
      ( r2_hidden(B_49,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ r2_hidden(D_54,k1_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | ~ r2_hidden(D_54,A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_151])).

tff(c_162,plain,(
    ! [B_49,A_48,D_54] :
      ( r2_hidden(B_49,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ r2_hidden(D_54,A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_158])).

tff(c_479,plain,(
    ! [B_155,A_156,C_157] :
      ( r2_hidden(B_155,k2_relat_1('#skF_6'(k1_relat_1(A_156),B_155)))
      | ~ r2_hidden(C_157,k2_relat_1(A_156))
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(resolution,[status(thm)],[c_235,c_162])).

tff(c_549,plain,(
    ! [B_164,A_165,B_166] :
      ( r2_hidden(B_164,k2_relat_1('#skF_6'(k1_relat_1(A_165),B_164)))
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165)
      | r1_tarski(k2_relat_1(A_165),B_166) ) ),
    inference(resolution,[status(thm)],[c_6,c_479])).

tff(c_579,plain,(
    ! [B_164,A_48,B_49,B_166] :
      ( r2_hidden(B_164,k2_relat_1('#skF_6'(A_48,B_164)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | r1_tarski(k2_relat_1('#skF_6'(A_48,B_49)),B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_549])).

tff(c_596,plain,(
    ! [B_167,A_168,B_169,B_170] :
      ( r2_hidden(B_167,k2_relat_1('#skF_6'(A_168,B_167)))
      | r1_tarski(k2_relat_1('#skF_6'(A_168,B_169)),B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_579])).

tff(c_626,plain,(
    ! [B_167,A_48,B_170] :
      ( r2_hidden(B_167,k2_relat_1('#skF_6'(A_48,B_167)))
      | r1_tarski(k2_relat_1(k1_xboole_0),B_170)
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_596])).

tff(c_743,plain,(
    ! [B_183,A_184] :
      ( r2_hidden(B_183,k2_relat_1('#skF_6'(A_184,B_183)))
      | k1_xboole_0 != A_184 ) ),
    inference(splitLeft,[status(thm)],[c_626])).

tff(c_756,plain,(
    ! [B_49,A_48] :
      ( r2_hidden(B_49,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_48
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_743])).

tff(c_764,plain,(
    ! [A_48] :
      ( k1_xboole_0 != A_48
      | k1_xboole_0 != A_48 ) ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_770,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_764])).

tff(c_771,plain,(
    ! [B_49] : r2_hidden(B_49,k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_244,plain,(
    ! [A_48,B_49,C_103] :
      ( r2_hidden('#skF_5'('#skF_6'(A_48,B_49),k2_relat_1('#skF_6'(A_48,B_49)),C_103),A_48)
      | ~ r2_hidden(C_103,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_235])).

tff(c_249,plain,(
    ! [A_48,B_49,C_103] :
      ( r2_hidden('#skF_5'('#skF_6'(A_48,B_49),k2_relat_1('#skF_6'(A_48,B_49)),C_103),A_48)
      | ~ r2_hidden(C_103,k2_relat_1('#skF_6'(A_48,B_49))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_244])).

tff(c_185,plain,(
    ! [A_95,C_96] :
      ( k1_funct_1(A_95,'#skF_5'(A_95,k2_relat_1(A_95),C_96)) = C_96
      | ~ r2_hidden(C_96,k2_relat_1(A_95))
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_195,plain,(
    ! [C_96,B_49,A_48] :
      ( C_96 = B_49
      | ~ r2_hidden('#skF_5'('#skF_6'(A_48,B_49),k2_relat_1('#skF_6'(A_48,B_49)),C_96),A_48)
      | ~ r2_hidden(C_96,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_32])).

tff(c_1488,plain,(
    ! [C_274,B_275,A_276] :
      ( C_274 = B_275
      | ~ r2_hidden('#skF_5'('#skF_6'(A_276,B_275),k2_relat_1('#skF_6'(A_276,B_275)),C_274),A_276)
      | ~ r2_hidden(C_274,k2_relat_1('#skF_6'(A_276,B_275))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_195])).

tff(c_1504,plain,(
    ! [C_277,B_278,A_279] :
      ( C_277 = B_278
      | ~ r2_hidden(C_277,k2_relat_1('#skF_6'(A_279,B_278))) ) ),
    inference(resolution,[status(thm)],[c_249,c_1488])).

tff(c_1577,plain,(
    ! [C_277,B_49,A_48] :
      ( C_277 = B_49
      | ~ r2_hidden(C_277,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_1504])).

tff(c_1616,plain,(
    ! [C_277,B_49,A_48] :
      ( C_277 = B_49
      | k1_xboole_0 != A_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_1577])).

tff(c_1617,plain,(
    ! [A_48] : k1_xboole_0 != A_48 ),
    inference(splitLeft,[status(thm)],[c_1616])).

tff(c_1625,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1617])).

tff(c_1674,plain,(
    ! [C_284,B_285] : C_284 = B_285 ),
    inference(splitRight,[status(thm)],[c_1616])).

tff(c_9606,plain,(
    ! [C_284] : C_284 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1674,c_44])).

tff(c_10087,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_9606])).

tff(c_10088,plain,(
    ! [B_170] : r1_tarski(k2_relat_1(k1_xboole_0),B_170) ),
    inference(splitRight,[status(thm)],[c_626])).

tff(c_63,plain,(
    ! [A_65,B_66] :
      ( k1_xboole_0 != A_65
      | '#skF_6'(A_65,B_66) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_59])).

tff(c_73,plain,(
    ! [A_65] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_36])).

tff(c_93,plain,(
    ! [A_65] : k1_xboole_0 != A_65 ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_99,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_93])).

tff(c_100,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_111,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_34])).

tff(c_71,plain,(
    ! [A_65] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_38])).

tff(c_79,plain,(
    ! [A_65] : k1_xboole_0 != A_65 ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_86,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_79])).

tff(c_87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_163,plain,(
    ! [B_89,A_90,D_91] :
      ( r2_hidden(B_89,k2_relat_1('#skF_6'(A_90,B_89)))
      | ~ r2_hidden(D_91,A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_158])).

tff(c_170,plain,(
    ! [B_92,A_93,B_94] :
      ( r2_hidden(B_92,k2_relat_1('#skF_6'(A_93,B_92)))
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_163])).

tff(c_180,plain,(
    ! [B_49,A_48,B_94] :
      ( r2_hidden(B_49,k2_relat_1(k1_xboole_0))
      | r1_tarski(A_48,B_94)
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_170])).

tff(c_211,plain,(
    ! [A_97,B_98] :
      ( r1_tarski(A_97,B_98)
      | k1_xboole_0 != A_97 ) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_40,plain,(
    ! [C_56] :
      ( ~ r1_tarski(k2_relat_1(C_56),'#skF_7')
      | k1_relat_1(C_56) != '#skF_8'
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_216,plain,(
    ! [C_99] :
      ( k1_relat_1(C_99) != '#skF_8'
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99)
      | k2_relat_1(C_99) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_211,c_40])).

tff(c_219,plain,
    ( k1_relat_1(k1_xboole_0) != '#skF_8'
    | ~ v1_funct_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_216])).

tff(c_225,plain,
    ( k1_xboole_0 != '#skF_8'
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_111,c_219])).

tff(c_229,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_62,plain,(
    ! [B_49] : '#skF_6'(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_59])).

tff(c_323,plain,(
    ! [A_129,B_130] :
      ( r2_hidden('#skF_3'(A_129,B_130),k1_relat_1(A_129))
      | r2_hidden('#skF_4'(A_129,B_130),B_130)
      | k2_relat_1(A_129) = B_130
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_338,plain,(
    ! [A_48,B_49,B_130] :
      ( r2_hidden('#skF_3'('#skF_6'(A_48,B_49),B_130),A_48)
      | r2_hidden('#skF_4'('#skF_6'(A_48,B_49),B_130),B_130)
      | k2_relat_1('#skF_6'(A_48,B_49)) = B_130
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_323])).

tff(c_11107,plain,(
    ! [A_2798,B_2799,B_2800] :
      ( r2_hidden('#skF_3'('#skF_6'(A_2798,B_2799),B_2800),A_2798)
      | r2_hidden('#skF_4'('#skF_6'(A_2798,B_2799),B_2800),B_2800)
      | k2_relat_1('#skF_6'(A_2798,B_2799)) = B_2800 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_338])).

tff(c_14,plain,(
    ! [A_8,D_47] :
      ( r2_hidden(k1_funct_1(A_8,D_47),k2_relat_1(A_8))
      | ~ r2_hidden(D_47,k1_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10759,plain,(
    ! [A_2781,B_2782,C_2783] :
      ( r2_hidden('#skF_5'('#skF_6'(A_2781,B_2782),k2_relat_1('#skF_6'(A_2781,B_2782)),C_2783),A_2781)
      | ~ r2_hidden(C_2783,k2_relat_1('#skF_6'(A_2781,B_2782))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_244])).

tff(c_576,plain,(
    ! [B_49,A_165,B_166] :
      ( r2_hidden(B_49,k2_relat_1(k1_xboole_0))
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165)
      | r1_tarski(k2_relat_1(A_165),B_166)
      | k1_relat_1(A_165) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_549])).

tff(c_10392,plain,(
    ! [A_165,B_166] :
      ( ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165)
      | r1_tarski(k2_relat_1(A_165),B_166)
      | k1_relat_1(A_165) != k1_xboole_0 ) ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10502,plain,(
    ! [A_2757,D_2758,B_2759] :
      ( r2_hidden(k1_funct_1(A_2757,D_2758),B_2759)
      | ~ r1_tarski(k2_relat_1(A_2757),B_2759)
      | ~ r2_hidden(D_2758,k1_relat_1(A_2757))
      | ~ v1_funct_1(A_2757)
      | ~ v1_relat_1(A_2757) ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_10525,plain,(
    ! [B_49,B_2759,A_48,D_54] :
      ( r2_hidden(B_49,B_2759)
      | ~ r1_tarski(k2_relat_1('#skF_6'(A_48,B_49)),B_2759)
      | ~ r2_hidden(D_54,k1_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | ~ r2_hidden(D_54,A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10502])).

tff(c_10534,plain,(
    ! [B_2760,B_2761,A_2762,D_2763] :
      ( r2_hidden(B_2760,B_2761)
      | ~ r1_tarski(k2_relat_1('#skF_6'(A_2762,B_2760)),B_2761)
      | ~ r2_hidden(D_2763,A_2762) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_10525])).

tff(c_10540,plain,(
    ! [B_2760,B_166,D_2763,A_2762] :
      ( r2_hidden(B_2760,B_166)
      | ~ r2_hidden(D_2763,A_2762)
      | ~ v1_funct_1('#skF_6'(A_2762,B_2760))
      | ~ v1_relat_1('#skF_6'(A_2762,B_2760))
      | k1_relat_1('#skF_6'(A_2762,B_2760)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10392,c_10534])).

tff(c_10565,plain,(
    ! [B_2760,B_166,D_2763,A_2762] :
      ( r2_hidden(B_2760,B_166)
      | ~ r2_hidden(D_2763,A_2762)
      | k1_xboole_0 != A_2762 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38,c_36,c_10540])).

tff(c_10577,plain,(
    ! [D_2763,A_2762] :
      ( ~ r2_hidden(D_2763,A_2762)
      | k1_xboole_0 != A_2762 ) ),
    inference(splitLeft,[status(thm)],[c_10565])).

tff(c_10791,plain,(
    ! [A_2784,C_2785,B_2786] :
      ( k1_xboole_0 != A_2784
      | ~ r2_hidden(C_2785,k2_relat_1('#skF_6'(A_2784,B_2786))) ) ),
    inference(resolution,[status(thm)],[c_10759,c_10577])).

tff(c_10852,plain,(
    ! [A_48,C_2785] :
      ( k1_xboole_0 != A_48
      | ~ r2_hidden(C_2785,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_10791])).

tff(c_10872,plain,(
    ! [A_48] :
      ( k1_xboole_0 != A_48
      | k1_xboole_0 != A_48 ) ),
    inference(splitLeft,[status(thm)],[c_10852])).

tff(c_10878,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10872])).

tff(c_10944,plain,(
    ! [C_2792] : ~ r2_hidden(C_2792,k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_10852])).

tff(c_10966,plain,(
    ! [D_47] :
      ( ~ r2_hidden(D_47,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_10944])).

tff(c_10977,plain,(
    ! [D_47] : ~ r2_hidden(D_47,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_100,c_111,c_10966])).

tff(c_11115,plain,(
    ! [B_2799,B_2800] :
      ( r2_hidden('#skF_4'('#skF_6'(k1_xboole_0,B_2799),B_2800),B_2800)
      | k2_relat_1('#skF_6'(k1_xboole_0,B_2799)) = B_2800 ) ),
    inference(resolution,[status(thm)],[c_11107,c_10977])).

tff(c_11246,plain,(
    ! [B_2803] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_2803),B_2803)
      | k2_relat_1(k1_xboole_0) = B_2803 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_11115])).

tff(c_11254,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11246,c_10977])).

tff(c_11284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_11254])).

tff(c_11285,plain,(
    ! [B_2760,B_166] : r2_hidden(B_2760,B_166) ),
    inference(splitRight,[status(thm)],[c_10565])).

tff(c_130,plain,(
    ! [A_79,B_80,D_81] :
      ( k1_funct_1('#skF_6'(A_79,B_80),D_81) = B_80
      | ~ r2_hidden(D_81,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_139,plain,(
    ! [D_81,B_49,A_48] :
      ( k1_funct_1(k1_xboole_0,D_81) = B_49
      | ~ r2_hidden(D_81,A_48)
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_130])).

tff(c_11334,plain,(
    ! [D_81,B_49,A_48] :
      ( k1_funct_1(k1_xboole_0,D_81) = B_49
      | k1_xboole_0 != A_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11285,c_139])).

tff(c_11356,plain,(
    ! [A_48] : k1_xboole_0 != A_48 ),
    inference(splitLeft,[status(thm)],[c_11334])).

tff(c_11364,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11356])).

tff(c_11381,plain,(
    ! [D_2808] : k1_funct_1(k1_xboole_0,D_2808) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_11334])).

tff(c_11365,plain,(
    ! [D_81,B_49] : k1_funct_1(k1_xboole_0,D_81) = B_49 ),
    inference(splitRight,[status(thm)],[c_11334])).

tff(c_11495,plain,(
    ! [B_3167] : B_3167 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_11381,c_11365])).

tff(c_620,plain,(
    ! [A_168,B_169,B_167] :
      ( k1_relat_1('#skF_6'(A_168,B_169)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_168,B_169))
      | ~ v1_relat_1('#skF_6'(A_168,B_169))
      | r2_hidden(B_167,k2_relat_1('#skF_6'(A_168,B_167))) ) ),
    inference(resolution,[status(thm)],[c_596,c_40])).

tff(c_643,plain,(
    ! [A_171,B_172] :
      ( A_171 != '#skF_8'
      | r2_hidden(B_172,k2_relat_1('#skF_6'(A_171,B_172))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_620])).

tff(c_656,plain,(
    ! [A_48,B_49] :
      ( A_48 != '#skF_8'
      | r2_hidden(B_49,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_643])).

tff(c_664,plain,(
    ! [A_48] :
      ( A_48 != '#skF_8'
      | k1_xboole_0 != A_48 ) ),
    inference(splitLeft,[status(thm)],[c_656])).

tff(c_668,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_664])).

tff(c_11543,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_11495,c_668])).

tff(c_11545,plain,(
    ! [B_3559] : r2_hidden(B_3559,k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_11562,plain,(
    ! [B_3559,B_2] :
      ( r2_hidden(B_3559,B_2)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),B_2) ) ),
    inference(resolution,[status(thm)],[c_11545,c_2])).

tff(c_11578,plain,(
    ! [B_3559,B_2] : r2_hidden(B_3559,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10088,c_11562])).

tff(c_11624,plain,(
    ! [D_81,B_49,A_48] :
      ( k1_funct_1(k1_xboole_0,D_81) = B_49
      | k1_xboole_0 != A_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11578,c_139])).

tff(c_11659,plain,(
    ! [A_48] : k1_xboole_0 != A_48 ),
    inference(splitLeft,[status(thm)],[c_11624])).

tff(c_11667,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11659])).

tff(c_11674,plain,(
    ! [D_3567] : k1_funct_1(k1_xboole_0,D_3567) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_11624])).

tff(c_11668,plain,(
    ! [D_81,B_49] : k1_funct_1(k1_xboole_0,D_81) = B_49 ),
    inference(splitRight,[status(thm)],[c_11624])).

tff(c_11814,plain,(
    ! [B_3943] : B_3943 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_11674,c_11668])).

tff(c_11866,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_11814,c_668])).

tff(c_11867,plain,(
    ! [B_49] : r2_hidden(B_49,k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_12742,plain,(
    ! [C_4464,B_4465,A_4466] :
      ( C_4464 = B_4465
      | ~ r2_hidden('#skF_5'('#skF_6'(A_4466,B_4465),k2_relat_1('#skF_6'(A_4466,B_4465)),C_4464),A_4466)
      | ~ r2_hidden(C_4464,k2_relat_1('#skF_6'(A_4466,B_4465))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_195])).

tff(c_12758,plain,(
    ! [C_4467,B_4468,A_4469] :
      ( C_4467 = B_4468
      | ~ r2_hidden(C_4467,k2_relat_1('#skF_6'(A_4469,B_4468))) ) ),
    inference(resolution,[status(thm)],[c_249,c_12742])).

tff(c_12831,plain,(
    ! [C_4467,B_49,A_48] :
      ( C_4467 = B_49
      | ~ r2_hidden(C_4467,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_12758])).

tff(c_12870,plain,(
    ! [C_4467,B_49,A_48] :
      ( C_4467 = B_49
      | k1_xboole_0 != A_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11867,c_12831])).

tff(c_12871,plain,(
    ! [A_48] : k1_xboole_0 != A_48 ),
    inference(splitLeft,[status(thm)],[c_12870])).

tff(c_12879,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12871])).

tff(c_12891,plain,(
    ! [C_4475,B_4476] : C_4475 = B_4476 ),
    inference(splitRight,[status(thm)],[c_12870])).

tff(c_20029,plain,(
    ! [C_4475] : k1_xboole_0 != C_4475 ),
    inference(superposition,[status(thm),theory(equality)],[c_12891,c_229])).

tff(c_20967,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_20029])).

tff(c_20969,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_21132,plain,(
    ! [A_6684,B_6685] :
      ( r2_hidden('#skF_3'(A_6684,B_6685),k1_relat_1(A_6684))
      | r2_hidden('#skF_4'(A_6684,B_6685),B_6685)
      | k2_relat_1(A_6684) = B_6685
      | ~ v1_funct_1(A_6684)
      | ~ v1_relat_1(A_6684) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_21149,plain,(
    ! [A_48,B_49,B_6685] :
      ( r2_hidden('#skF_3'('#skF_6'(A_48,B_49),B_6685),A_48)
      | r2_hidden('#skF_4'('#skF_6'(A_48,B_49),B_6685),B_6685)
      | k2_relat_1('#skF_6'(A_48,B_49)) = B_6685
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_21132])).

tff(c_22968,plain,(
    ! [A_6864,B_6865,B_6866] :
      ( r2_hidden('#skF_3'('#skF_6'(A_6864,B_6865),B_6866),A_6864)
      | r2_hidden('#skF_4'('#skF_6'(A_6864,B_6865),B_6866),B_6866)
      | k2_relat_1('#skF_6'(A_6864,B_6865)) = B_6866 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_21149])).

tff(c_20976,plain,(
    ! [D_47] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_47),k1_xboole_0)
      | ~ r2_hidden(D_47,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20969,c_14])).

tff(c_21020,plain,(
    ! [D_6658] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_6658),k1_xboole_0)
      | ~ r2_hidden(D_6658,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_100,c_111,c_20976])).

tff(c_21022,plain,(
    ! [B_49,D_6658] :
      ( r2_hidden(B_49,k2_relat_1('#skF_6'(k1_xboole_0,B_49)))
      | ~ r2_hidden(D_6658,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_21020,c_162])).

tff(c_21032,plain,(
    ! [B_49,D_6658] :
      ( r2_hidden(B_49,k1_xboole_0)
      | ~ r2_hidden(D_6658,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20969,c_62,c_21022])).

tff(c_21039,plain,(
    ! [D_6658] : ~ r2_hidden(D_6658,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_21032])).

tff(c_22995,plain,(
    ! [B_6865,B_6866] :
      ( r2_hidden('#skF_4'('#skF_6'(k1_xboole_0,B_6865),B_6866),B_6866)
      | k2_relat_1('#skF_6'(k1_xboole_0,B_6865)) = B_6866 ) ),
    inference(resolution,[status(thm)],[c_22968,c_21039])).

tff(c_23044,plain,(
    ! [B_6866] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_6866),B_6866)
      | k1_xboole_0 = B_6866 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20969,c_62,c_62,c_22995])).

tff(c_118,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [A_72] : r1_tarski(A_72,A_72) ),
    inference(resolution,[status(thm)],[c_118,c_4])).

tff(c_20995,plain,(
    ! [A_6655,C_6656] :
      ( r2_hidden('#skF_5'(A_6655,k2_relat_1(A_6655),C_6656),k1_relat_1(A_6655))
      | ~ r2_hidden(C_6656,k2_relat_1(A_6655))
      | ~ v1_funct_1(A_6655)
      | ~ v1_relat_1(A_6655) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_21010,plain,(
    ! [A_6655,C_6656,B_2] :
      ( r2_hidden('#skF_5'(A_6655,k2_relat_1(A_6655),C_6656),B_2)
      | ~ r1_tarski(k1_relat_1(A_6655),B_2)
      | ~ r2_hidden(C_6656,k2_relat_1(A_6655))
      | ~ v1_funct_1(A_6655)
      | ~ v1_relat_1(A_6655) ) ),
    inference(resolution,[status(thm)],[c_20995,c_2])).

tff(c_202,plain,(
    ! [C_96,B_49,A_48] :
      ( C_96 = B_49
      | ~ r2_hidden(C_96,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_48,B_49),k2_relat_1('#skF_6'(A_48,B_49)),C_96),A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_185])).

tff(c_24776,plain,(
    ! [C_6905,B_6906,A_6907] :
      ( C_6905 = B_6906
      | ~ r2_hidden(C_6905,k2_relat_1('#skF_6'(A_6907,B_6906)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_6907,B_6906),k2_relat_1('#skF_6'(A_6907,B_6906)),C_6905),A_6907) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_202])).

tff(c_24789,plain,(
    ! [C_6656,B_6906,B_2] :
      ( C_6656 = B_6906
      | ~ r1_tarski(k1_relat_1('#skF_6'(B_2,B_6906)),B_2)
      | ~ r2_hidden(C_6656,k2_relat_1('#skF_6'(B_2,B_6906)))
      | ~ v1_funct_1('#skF_6'(B_2,B_6906))
      | ~ v1_relat_1('#skF_6'(B_2,B_6906)) ) ),
    inference(resolution,[status(thm)],[c_21010,c_24776])).

tff(c_24808,plain,(
    ! [C_6908,B_6909,B_6910] :
      ( C_6908 = B_6909
      | ~ r2_hidden(C_6908,k2_relat_1('#skF_6'(B_6910,B_6909))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_123,c_34,c_24789])).

tff(c_39407,plain,(
    ! [B_9994,B_9995,B_9996] :
      ( '#skF_1'(k2_relat_1('#skF_6'(B_9994,B_9995)),B_9996) = B_9995
      | r1_tarski(k2_relat_1('#skF_6'(B_9994,B_9995)),B_9996) ) ),
    inference(resolution,[status(thm)],[c_6,c_24808])).

tff(c_39533,plain,(
    ! [B_9994,B_9995] :
      ( k1_relat_1('#skF_6'(B_9994,B_9995)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(B_9994,B_9995))
      | ~ v1_relat_1('#skF_6'(B_9994,B_9995))
      | '#skF_1'(k2_relat_1('#skF_6'(B_9994,B_9995)),'#skF_7') = B_9995 ) ),
    inference(resolution,[status(thm)],[c_39407,c_40])).

tff(c_39677,plain,(
    ! [B_10014,B_10015] :
      ( B_10014 != '#skF_8'
      | '#skF_1'(k2_relat_1('#skF_6'(B_10014,B_10015)),'#skF_7') = B_10015 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_39533])).

tff(c_39873,plain,(
    ! [B_10052,B_10053] :
      ( ~ r2_hidden(B_10052,'#skF_7')
      | r1_tarski(k2_relat_1('#skF_6'(B_10053,B_10052)),'#skF_7')
      | B_10053 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39677,c_4])).

tff(c_39912,plain,(
    ! [B_10053,B_10052] :
      ( k1_relat_1('#skF_6'(B_10053,B_10052)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(B_10053,B_10052))
      | ~ v1_relat_1('#skF_6'(B_10053,B_10052))
      | ~ r2_hidden(B_10052,'#skF_7')
      | B_10053 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_39873,c_40])).

tff(c_40000,plain,(
    ! [B_10052,B_10053] :
      ( ~ r2_hidden(B_10052,'#skF_7')
      | B_10053 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_39912])).

tff(c_40015,plain,(
    ! [B_10053] : B_10053 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_40000])).

tff(c_40019,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_40015])).

tff(c_40022,plain,(
    ! [B_10071] : ~ r2_hidden(B_10071,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_40000])).

tff(c_40046,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_23044,c_40022])).

tff(c_40082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40046])).

tff(c_40086,plain,(
    ! [B_10089] : r2_hidden(B_10089,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_21032])).

tff(c_40251,plain,(
    ! [B_10089] : k1_funct_1(k1_xboole_0,B_10089) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_40086,c_139])).

tff(c_40140,plain,(
    ! [B_10097,B_10098] : k1_funct_1(k1_xboole_0,B_10097) = B_10098 ),
    inference(resolution,[status(thm)],[c_40086,c_139])).

tff(c_40328,plain,(
    ! [B_10747] : B_10747 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_40251,c_40140])).

tff(c_20968,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_40360,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_40328,c_20968])).

tff(c_40361,plain,(
    ! [B_49] : r2_hidden(B_49,k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_40434,plain,(
    ! [A_11078,C_11079] :
      ( r2_hidden('#skF_5'(A_11078,k2_relat_1(A_11078),C_11079),k1_relat_1(A_11078))
      | ~ r2_hidden(C_11079,k2_relat_1(A_11078))
      | ~ v1_funct_1(A_11078)
      | ~ v1_relat_1(A_11078) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40446,plain,(
    ! [A_11078,C_11079,B_2] :
      ( r2_hidden('#skF_5'(A_11078,k2_relat_1(A_11078),C_11079),B_2)
      | ~ r1_tarski(k1_relat_1(A_11078),B_2)
      | ~ r2_hidden(C_11079,k2_relat_1(A_11078))
      | ~ v1_funct_1(A_11078)
      | ~ v1_relat_1(A_11078) ) ),
    inference(resolution,[status(thm)],[c_40434,c_2])).

tff(c_40393,plain,(
    ! [A_11074,C_11075] :
      ( k1_funct_1(A_11074,'#skF_5'(A_11074,k2_relat_1(A_11074),C_11075)) = C_11075
      | ~ r2_hidden(C_11075,k2_relat_1(A_11074))
      | ~ v1_funct_1(A_11074)
      | ~ v1_relat_1(A_11074) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40410,plain,(
    ! [C_11075,B_49,A_48] :
      ( C_11075 = B_49
      | ~ r2_hidden(C_11075,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_48,B_49),k2_relat_1('#skF_6'(A_48,B_49)),C_11075),A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_40393])).

tff(c_41934,plain,(
    ! [C_12050,B_12051,A_12052] :
      ( C_12050 = B_12051
      | ~ r2_hidden(C_12050,k2_relat_1('#skF_6'(A_12052,B_12051)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_12052,B_12051),k2_relat_1('#skF_6'(A_12052,B_12051)),C_12050),A_12052) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_40410])).

tff(c_41938,plain,(
    ! [C_11079,B_12051,B_2] :
      ( C_11079 = B_12051
      | ~ r1_tarski(k1_relat_1('#skF_6'(B_2,B_12051)),B_2)
      | ~ r2_hidden(C_11079,k2_relat_1('#skF_6'(B_2,B_12051)))
      | ~ v1_funct_1('#skF_6'(B_2,B_12051))
      | ~ v1_relat_1('#skF_6'(B_2,B_12051)) ) ),
    inference(resolution,[status(thm)],[c_40446,c_41934])).

tff(c_41957,plain,(
    ! [C_12053,B_12054,B_12055] :
      ( C_12053 = B_12054
      | ~ r2_hidden(C_12053,k2_relat_1('#skF_6'(B_12055,B_12054))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_123,c_34,c_41938])).

tff(c_42030,plain,(
    ! [C_12053,B_49,A_48] :
      ( C_12053 = B_49
      | ~ r2_hidden(C_12053,k2_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_41957])).

tff(c_42064,plain,(
    ! [C_12053,B_49,A_48] :
      ( C_12053 = B_49
      | k1_xboole_0 != A_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40361,c_42030])).

tff(c_42065,plain,(
    ! [A_48] : k1_xboole_0 != A_48 ),
    inference(splitLeft,[status(thm)],[c_42064])).

tff(c_42073,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_42065])).

tff(c_42111,plain,(
    ! [C_12060,B_12061] : C_12060 = B_12061 ),
    inference(splitRight,[status(thm)],[c_42064])).

tff(c_48605,plain,(
    ! [B_12061] : B_12061 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_42111,c_44])).

tff(c_48791,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_48605])).

tff(c_48792,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_relat_1(A_7) != k1_xboole_0
      | k1_xboole_0 = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48825,plain,(
    ! [A_14043] :
      ( k1_relat_1(A_14043) != '#skF_8'
      | A_14043 = '#skF_8'
      | ~ v1_relat_1(A_14043) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48792,c_48792,c_12])).

tff(c_48828,plain,(
    ! [A_48,B_49] :
      ( k1_relat_1('#skF_6'(A_48,B_49)) != '#skF_8'
      | '#skF_6'(A_48,B_49) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_38,c_48825])).

tff(c_48832,plain,(
    ! [A_14044,B_14045] :
      ( A_14044 != '#skF_8'
      | '#skF_6'(A_14044,B_14045) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48828])).

tff(c_48840,plain,(
    ! [A_14044] :
      ( v1_relat_1('#skF_8')
      | A_14044 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48832,c_38])).

tff(c_48848,plain,(
    ! [A_14044] : A_14044 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_48840])).

tff(c_48793,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_48800,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48792,c_48793])).

tff(c_48855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48848,c_48800])).

tff(c_48856,plain,(
    v1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_48840])).

tff(c_48842,plain,(
    ! [A_14044] :
      ( v1_funct_1('#skF_8')
      | A_14044 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48832,c_36])).

tff(c_48867,plain,(
    ! [A_14044] : A_14044 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_48842])).

tff(c_48873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48867,c_48800])).

tff(c_48874,plain,(
    v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_48842])).

tff(c_48876,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_48832,c_34])).

tff(c_48882,plain,(
    ! [A_14050,B_14051] :
      ( r2_hidden('#skF_1'(A_14050,B_14051),A_14050)
      | r1_tarski(A_14050,B_14051) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48887,plain,(
    ! [A_14050] : r1_tarski(A_14050,A_14050) ),
    inference(resolution,[status(thm)],[c_48882,c_4])).

tff(c_48830,plain,(
    ! [A_48,B_49] :
      ( A_48 != '#skF_8'
      | '#skF_6'(A_48,B_49) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48828])).

tff(c_49013,plain,(
    ! [A_14083,C_14084] :
      ( r2_hidden('#skF_5'(A_14083,k2_relat_1(A_14083),C_14084),k1_relat_1(A_14083))
      | ~ r2_hidden(C_14084,k2_relat_1(A_14083))
      | ~ v1_funct_1(A_14083)
      | ~ v1_relat_1(A_14083) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48927,plain,(
    ! [A_14068,D_14069] :
      ( r2_hidden(k1_funct_1(A_14068,D_14069),k2_relat_1(A_14068))
      | ~ r2_hidden(D_14069,k1_relat_1(A_14068))
      | ~ v1_funct_1(A_14068)
      | ~ v1_relat_1(A_14068) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48934,plain,(
    ! [B_49,A_48,D_54] :
      ( r2_hidden(B_49,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ r2_hidden(D_54,k1_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | ~ r2_hidden(D_54,A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_48927])).

tff(c_48938,plain,(
    ! [B_49,A_48,D_54] :
      ( r2_hidden(B_49,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ r2_hidden(D_54,A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_48934])).

tff(c_49242,plain,(
    ! [B_14133,A_14134,C_14135] :
      ( r2_hidden(B_14133,k2_relat_1('#skF_6'(k1_relat_1(A_14134),B_14133)))
      | ~ r2_hidden(C_14135,k2_relat_1(A_14134))
      | ~ v1_funct_1(A_14134)
      | ~ v1_relat_1(A_14134) ) ),
    inference(resolution,[status(thm)],[c_49013,c_48938])).

tff(c_49311,plain,(
    ! [B_14139,A_14140,B_14141] :
      ( r2_hidden(B_14139,k2_relat_1('#skF_6'(k1_relat_1(A_14140),B_14139)))
      | ~ v1_funct_1(A_14140)
      | ~ v1_relat_1(A_14140)
      | r1_tarski(k2_relat_1(A_14140),B_14141) ) ),
    inference(resolution,[status(thm)],[c_6,c_49242])).

tff(c_49341,plain,(
    ! [B_14139,A_48,B_49,B_14141] :
      ( r2_hidden(B_14139,k2_relat_1('#skF_6'(A_48,B_14139)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | r1_tarski(k2_relat_1('#skF_6'(A_48,B_49)),B_14141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_49311])).

tff(c_49358,plain,(
    ! [B_14142,A_14143,B_14144,B_14145] :
      ( r2_hidden(B_14142,k2_relat_1('#skF_6'(A_14143,B_14142)))
      | r1_tarski(k2_relat_1('#skF_6'(A_14143,B_14144)),B_14145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_49341])).

tff(c_48801,plain,(
    ! [C_56] :
      ( ~ r1_tarski(k2_relat_1(C_56),'#skF_8')
      | k1_relat_1(C_56) != '#skF_8'
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48800,c_40])).

tff(c_49382,plain,(
    ! [A_14143,B_14144,B_14142] :
      ( k1_relat_1('#skF_6'(A_14143,B_14144)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_14143,B_14144))
      | ~ v1_relat_1('#skF_6'(A_14143,B_14144))
      | r2_hidden(B_14142,k2_relat_1('#skF_6'(A_14143,B_14142))) ) ),
    inference(resolution,[status(thm)],[c_49358,c_48801])).

tff(c_49406,plain,(
    ! [A_14149,B_14150] :
      ( A_14149 != '#skF_8'
      | r2_hidden(B_14150,k2_relat_1('#skF_6'(A_14149,B_14150))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_49382])).

tff(c_49419,plain,(
    ! [A_48,B_49] :
      ( A_48 != '#skF_8'
      | r2_hidden(B_49,k2_relat_1('#skF_8'))
      | A_48 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48830,c_49406])).

tff(c_49427,plain,(
    ! [A_48] :
      ( A_48 != '#skF_8'
      | A_48 != '#skF_8' ) ),
    inference(splitLeft,[status(thm)],[c_49419])).

tff(c_49433,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_49427])).

tff(c_49434,plain,(
    ! [B_49] : r2_hidden(B_49,k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_49419])).

tff(c_49025,plain,(
    ! [A_14083,C_14084,B_2] :
      ( r2_hidden('#skF_5'(A_14083,k2_relat_1(A_14083),C_14084),B_2)
      | ~ r1_tarski(k1_relat_1(A_14083),B_2)
      | ~ r2_hidden(C_14084,k2_relat_1(A_14083))
      | ~ v1_funct_1(A_14083)
      | ~ v1_relat_1(A_14083) ) ),
    inference(resolution,[status(thm)],[c_49013,c_2])).

tff(c_48964,plain,(
    ! [A_14076,C_14077] :
      ( k1_funct_1(A_14076,'#skF_5'(A_14076,k2_relat_1(A_14076),C_14077)) = C_14077
      | ~ r2_hidden(C_14077,k2_relat_1(A_14076))
      | ~ v1_funct_1(A_14076)
      | ~ v1_relat_1(A_14076) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48981,plain,(
    ! [C_14077,B_49,A_48] :
      ( C_14077 = B_49
      | ~ r2_hidden(C_14077,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_48,B_49),k2_relat_1('#skF_6'(A_48,B_49)),C_14077),A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_48964])).

tff(c_50792,plain,(
    ! [C_14305,B_14306,A_14307] :
      ( C_14305 = B_14306
      | ~ r2_hidden(C_14305,k2_relat_1('#skF_6'(A_14307,B_14306)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_14307,B_14306),k2_relat_1('#skF_6'(A_14307,B_14306)),C_14305),A_14307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_48981])).

tff(c_50796,plain,(
    ! [C_14084,B_14306,B_2] :
      ( C_14084 = B_14306
      | ~ r1_tarski(k1_relat_1('#skF_6'(B_2,B_14306)),B_2)
      | ~ r2_hidden(C_14084,k2_relat_1('#skF_6'(B_2,B_14306)))
      | ~ v1_funct_1('#skF_6'(B_2,B_14306))
      | ~ v1_relat_1('#skF_6'(B_2,B_14306)) ) ),
    inference(resolution,[status(thm)],[c_49025,c_50792])).

tff(c_50815,plain,(
    ! [C_14308,B_14309,B_14310] :
      ( C_14308 = B_14309
      | ~ r2_hidden(C_14308,k2_relat_1('#skF_6'(B_14310,B_14309))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_48887,c_34,c_50796])).

tff(c_50895,plain,(
    ! [C_14308,B_49,A_48] :
      ( C_14308 = B_49
      | ~ r2_hidden(C_14308,k2_relat_1('#skF_8'))
      | A_48 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48830,c_50815])).

tff(c_50937,plain,(
    ! [C_14308,B_49,A_48] :
      ( C_14308 = B_49
      | A_48 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49434,c_50895])).

tff(c_50938,plain,(
    ! [A_48] : A_48 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_50937])).

tff(c_50945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50938,c_48800])).

tff(c_51013,plain,(
    ! [C_14316,B_14317] : C_14316 = B_14317 ),
    inference(splitRight,[status(thm)],[c_50937])).

tff(c_48939,plain,(
    ! [B_14070,A_14071,D_14072] :
      ( r2_hidden(B_14070,k2_relat_1('#skF_6'(A_14071,B_14070)))
      | ~ r2_hidden(D_14072,A_14071) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_48934])).

tff(c_48949,plain,(
    ! [B_14073,A_14074,B_14075] :
      ( r2_hidden(B_14073,k2_relat_1('#skF_6'(A_14074,B_14073)))
      | r1_tarski(A_14074,B_14075) ) ),
    inference(resolution,[status(thm)],[c_6,c_48939])).

tff(c_48959,plain,(
    ! [B_49,A_48,B_14075] :
      ( r2_hidden(B_49,k2_relat_1('#skF_8'))
      | r1_tarski(A_48,B_14075)
      | A_48 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48830,c_48949])).

tff(c_48990,plain,(
    ! [A_14078,B_14079] :
      ( r1_tarski(A_14078,B_14079)
      | A_14078 != '#skF_8' ) ),
    inference(splitLeft,[status(thm)],[c_48959])).

tff(c_48995,plain,(
    ! [C_14080] :
      ( k1_relat_1(C_14080) != '#skF_8'
      | ~ v1_funct_1(C_14080)
      | ~ v1_relat_1(C_14080)
      | k2_relat_1(C_14080) != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_48990,c_48801])).

tff(c_48998,plain,
    ( k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | k2_relat_1('#skF_8') != '#skF_8' ),
    inference(resolution,[status(thm)],[c_48856,c_48995])).

tff(c_49004,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48874,c_48876,c_48998])).

tff(c_59915,plain,(
    ! [C_14316] : C_14316 != '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_51013,c_49004])).

tff(c_61062,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_59915])).

tff(c_61063,plain,(
    ! [B_49] : r2_hidden(B_49,k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_48959])).

tff(c_61136,plain,(
    ! [A_16807,C_16808] :
      ( r2_hidden('#skF_5'(A_16807,k2_relat_1(A_16807),C_16808),k1_relat_1(A_16807))
      | ~ r2_hidden(C_16808,k2_relat_1(A_16807))
      | ~ v1_funct_1(A_16807)
      | ~ v1_relat_1(A_16807) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61148,plain,(
    ! [A_16807,C_16808,B_2] :
      ( r2_hidden('#skF_5'(A_16807,k2_relat_1(A_16807),C_16808),B_2)
      | ~ r1_tarski(k1_relat_1(A_16807),B_2)
      | ~ r2_hidden(C_16808,k2_relat_1(A_16807))
      | ~ v1_funct_1(A_16807)
      | ~ v1_relat_1(A_16807) ) ),
    inference(resolution,[status(thm)],[c_61136,c_2])).

tff(c_61095,plain,(
    ! [A_16803,C_16804] :
      ( k1_funct_1(A_16803,'#skF_5'(A_16803,k2_relat_1(A_16803),C_16804)) = C_16804
      | ~ r2_hidden(C_16804,k2_relat_1(A_16803))
      | ~ v1_funct_1(A_16803)
      | ~ v1_relat_1(A_16803) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61105,plain,(
    ! [C_16804,B_49,A_48] :
      ( C_16804 = B_49
      | ~ r2_hidden('#skF_5'('#skF_6'(A_48,B_49),k2_relat_1('#skF_6'(A_48,B_49)),C_16804),A_48)
      | ~ r2_hidden(C_16804,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61095,c_32])).

tff(c_62455,plain,(
    ! [C_17717,B_17718,A_17719] :
      ( C_17717 = B_17718
      | ~ r2_hidden('#skF_5'('#skF_6'(A_17719,B_17718),k2_relat_1('#skF_6'(A_17719,B_17718)),C_17717),A_17719)
      | ~ r2_hidden(C_17717,k2_relat_1('#skF_6'(A_17719,B_17718))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_61105])).

tff(c_62459,plain,(
    ! [C_16808,B_17718,B_2] :
      ( C_16808 = B_17718
      | ~ r1_tarski(k1_relat_1('#skF_6'(B_2,B_17718)),B_2)
      | ~ r2_hidden(C_16808,k2_relat_1('#skF_6'(B_2,B_17718)))
      | ~ v1_funct_1('#skF_6'(B_2,B_17718))
      | ~ v1_relat_1('#skF_6'(B_2,B_17718)) ) ),
    inference(resolution,[status(thm)],[c_61148,c_62455])).

tff(c_62478,plain,(
    ! [C_17720,B_17721,B_17722] :
      ( C_17720 = B_17721
      | ~ r2_hidden(C_17720,k2_relat_1('#skF_6'(B_17722,B_17721))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_48887,c_34,c_62459])).

tff(c_62537,plain,(
    ! [C_17720,B_49,A_48] :
      ( C_17720 = B_49
      | ~ r2_hidden(C_17720,k2_relat_1('#skF_8'))
      | A_48 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48830,c_62478])).

tff(c_62565,plain,(
    ! [C_17720,B_49,A_48] :
      ( C_17720 = B_49
      | A_48 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61063,c_62537])).

tff(c_62566,plain,(
    ! [A_48] : A_48 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_62565])).

tff(c_62573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62566,c_48800])).

tff(c_62623,plain,(
    ! [C_17726,B_17727] : C_17726 = B_17727 ),
    inference(splitRight,[status(thm)],[c_62565])).

tff(c_61064,plain,(
    ! [B_16800] : r2_hidden(B_16800,k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_48959])).

tff(c_48890,plain,(
    ! [A_14054,B_14055,D_14056] :
      ( k1_funct_1('#skF_6'(A_14054,B_14055),D_14056) = B_14055
      | ~ r2_hidden(D_14056,A_14054) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48899,plain,(
    ! [D_14056,B_49,A_48] :
      ( k1_funct_1('#skF_8',D_14056) = B_49
      | ~ r2_hidden(D_14056,A_48)
      | A_48 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48830,c_48890])).

tff(c_61076,plain,(
    ! [B_16800,B_49] :
      ( k1_funct_1('#skF_8',B_16800) = B_49
      | k2_relat_1('#skF_8') != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_61064,c_48899])).

tff(c_61119,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_61076])).

tff(c_66435,plain,(
    ! [B_17727] : B_17727 != '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_62623,c_61119])).

tff(c_68056,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_66435])).

tff(c_68058,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_61076])).

tff(c_68072,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_68058,c_48801])).

tff(c_68081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48856,c_48874,c_48876,c_48887,c_68072])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:59:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.69/5.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.69/5.48  
% 13.69/5.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.69/5.48  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 13.69/5.48  
% 13.69/5.48  %Foreground sorts:
% 13.69/5.48  
% 13.69/5.48  
% 13.69/5.48  %Background operators:
% 13.69/5.48  
% 13.69/5.48  
% 13.69/5.48  %Foreground operators:
% 13.69/5.48  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.69/5.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.69/5.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.69/5.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.69/5.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.69/5.48  tff('#skF_7', type, '#skF_7': $i).
% 13.69/5.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.69/5.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.69/5.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.69/5.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 13.69/5.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.69/5.48  tff('#skF_8', type, '#skF_8': $i).
% 13.69/5.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.69/5.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.69/5.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.69/5.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.69/5.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.69/5.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.69/5.48  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.69/5.48  
% 13.69/5.52  tff(f_69, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 13.69/5.52  tff(f_87, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 13.69/5.52  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 13.69/5.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.69/5.52  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 13.69/5.52  tff(c_34, plain, (![A_48, B_49]: (k1_relat_1('#skF_6'(A_48, B_49))=A_48)), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.69/5.52  tff(c_38, plain, (![A_48, B_49]: (v1_relat_1('#skF_6'(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.69/5.52  tff(c_42, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.69/5.52  tff(c_44, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_42])).
% 13.69/5.52  tff(c_56, plain, (![A_64]: (k1_relat_1(A_64)!=k1_xboole_0 | k1_xboole_0=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.69/5.52  tff(c_59, plain, (![A_48, B_49]: (k1_relat_1('#skF_6'(A_48, B_49))!=k1_xboole_0 | '#skF_6'(A_48, B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_56])).
% 13.69/5.52  tff(c_61, plain, (![A_48, B_49]: (k1_xboole_0!=A_48 | '#skF_6'(A_48, B_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_59])).
% 13.69/5.52  tff(c_36, plain, (![A_48, B_49]: (v1_funct_1('#skF_6'(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.69/5.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.69/5.52  tff(c_235, plain, (![A_102, C_103]: (r2_hidden('#skF_5'(A_102, k2_relat_1(A_102), C_103), k1_relat_1(A_102)) | ~r2_hidden(C_103, k2_relat_1(A_102)) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_32, plain, (![A_48, B_49, D_54]: (k1_funct_1('#skF_6'(A_48, B_49), D_54)=B_49 | ~r2_hidden(D_54, A_48))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.69/5.52  tff(c_151, plain, (![A_87, D_88]: (r2_hidden(k1_funct_1(A_87, D_88), k2_relat_1(A_87)) | ~r2_hidden(D_88, k1_relat_1(A_87)) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_158, plain, (![B_49, A_48, D_54]: (r2_hidden(B_49, k2_relat_1('#skF_6'(A_48, B_49))) | ~r2_hidden(D_54, k1_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | ~r2_hidden(D_54, A_48))), inference(superposition, [status(thm), theory('equality')], [c_32, c_151])).
% 13.69/5.52  tff(c_162, plain, (![B_49, A_48, D_54]: (r2_hidden(B_49, k2_relat_1('#skF_6'(A_48, B_49))) | ~r2_hidden(D_54, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_158])).
% 13.69/5.52  tff(c_479, plain, (![B_155, A_156, C_157]: (r2_hidden(B_155, k2_relat_1('#skF_6'(k1_relat_1(A_156), B_155))) | ~r2_hidden(C_157, k2_relat_1(A_156)) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(resolution, [status(thm)], [c_235, c_162])).
% 13.69/5.52  tff(c_549, plain, (![B_164, A_165, B_166]: (r2_hidden(B_164, k2_relat_1('#skF_6'(k1_relat_1(A_165), B_164))) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165) | r1_tarski(k2_relat_1(A_165), B_166))), inference(resolution, [status(thm)], [c_6, c_479])).
% 13.69/5.52  tff(c_579, plain, (![B_164, A_48, B_49, B_166]: (r2_hidden(B_164, k2_relat_1('#skF_6'(A_48, B_164))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | r1_tarski(k2_relat_1('#skF_6'(A_48, B_49)), B_166))), inference(superposition, [status(thm), theory('equality')], [c_34, c_549])).
% 13.69/5.52  tff(c_596, plain, (![B_167, A_168, B_169, B_170]: (r2_hidden(B_167, k2_relat_1('#skF_6'(A_168, B_167))) | r1_tarski(k2_relat_1('#skF_6'(A_168, B_169)), B_170))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_579])).
% 13.69/5.52  tff(c_626, plain, (![B_167, A_48, B_170]: (r2_hidden(B_167, k2_relat_1('#skF_6'(A_48, B_167))) | r1_tarski(k2_relat_1(k1_xboole_0), B_170) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_61, c_596])).
% 13.69/5.52  tff(c_743, plain, (![B_183, A_184]: (r2_hidden(B_183, k2_relat_1('#skF_6'(A_184, B_183))) | k1_xboole_0!=A_184)), inference(splitLeft, [status(thm)], [c_626])).
% 13.69/5.52  tff(c_756, plain, (![B_49, A_48]: (r2_hidden(B_49, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_48 | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_61, c_743])).
% 13.69/5.52  tff(c_764, plain, (![A_48]: (k1_xboole_0!=A_48 | k1_xboole_0!=A_48)), inference(splitLeft, [status(thm)], [c_756])).
% 13.69/5.52  tff(c_770, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_764])).
% 13.69/5.52  tff(c_771, plain, (![B_49]: (r2_hidden(B_49, k2_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_756])).
% 13.69/5.52  tff(c_244, plain, (![A_48, B_49, C_103]: (r2_hidden('#skF_5'('#skF_6'(A_48, B_49), k2_relat_1('#skF_6'(A_48, B_49)), C_103), A_48) | ~r2_hidden(C_103, k2_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_235])).
% 13.69/5.52  tff(c_249, plain, (![A_48, B_49, C_103]: (r2_hidden('#skF_5'('#skF_6'(A_48, B_49), k2_relat_1('#skF_6'(A_48, B_49)), C_103), A_48) | ~r2_hidden(C_103, k2_relat_1('#skF_6'(A_48, B_49))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_244])).
% 13.69/5.52  tff(c_185, plain, (![A_95, C_96]: (k1_funct_1(A_95, '#skF_5'(A_95, k2_relat_1(A_95), C_96))=C_96 | ~r2_hidden(C_96, k2_relat_1(A_95)) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_195, plain, (![C_96, B_49, A_48]: (C_96=B_49 | ~r2_hidden('#skF_5'('#skF_6'(A_48, B_49), k2_relat_1('#skF_6'(A_48, B_49)), C_96), A_48) | ~r2_hidden(C_96, k2_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_32])).
% 13.69/5.52  tff(c_1488, plain, (![C_274, B_275, A_276]: (C_274=B_275 | ~r2_hidden('#skF_5'('#skF_6'(A_276, B_275), k2_relat_1('#skF_6'(A_276, B_275)), C_274), A_276) | ~r2_hidden(C_274, k2_relat_1('#skF_6'(A_276, B_275))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_195])).
% 13.69/5.52  tff(c_1504, plain, (![C_277, B_278, A_279]: (C_277=B_278 | ~r2_hidden(C_277, k2_relat_1('#skF_6'(A_279, B_278))))), inference(resolution, [status(thm)], [c_249, c_1488])).
% 13.69/5.52  tff(c_1577, plain, (![C_277, B_49, A_48]: (C_277=B_49 | ~r2_hidden(C_277, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_61, c_1504])).
% 13.69/5.52  tff(c_1616, plain, (![C_277, B_49, A_48]: (C_277=B_49 | k1_xboole_0!=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_771, c_1577])).
% 13.69/5.52  tff(c_1617, plain, (![A_48]: (k1_xboole_0!=A_48)), inference(splitLeft, [status(thm)], [c_1616])).
% 13.69/5.52  tff(c_1625, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_1617])).
% 13.69/5.52  tff(c_1674, plain, (![C_284, B_285]: (C_284=B_285)), inference(splitRight, [status(thm)], [c_1616])).
% 13.69/5.52  tff(c_9606, plain, (![C_284]: (C_284!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1674, c_44])).
% 13.69/5.52  tff(c_10087, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_9606])).
% 13.69/5.52  tff(c_10088, plain, (![B_170]: (r1_tarski(k2_relat_1(k1_xboole_0), B_170))), inference(splitRight, [status(thm)], [c_626])).
% 13.69/5.52  tff(c_63, plain, (![A_65, B_66]: (k1_xboole_0!=A_65 | '#skF_6'(A_65, B_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_59])).
% 13.69/5.52  tff(c_73, plain, (![A_65]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_65)), inference(superposition, [status(thm), theory('equality')], [c_63, c_36])).
% 13.69/5.52  tff(c_93, plain, (![A_65]: (k1_xboole_0!=A_65)), inference(splitLeft, [status(thm)], [c_73])).
% 13.69/5.52  tff(c_99, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_93])).
% 13.69/5.52  tff(c_100, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_73])).
% 13.69/5.52  tff(c_111, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_63, c_34])).
% 13.69/5.52  tff(c_71, plain, (![A_65]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_65)), inference(superposition, [status(thm), theory('equality')], [c_63, c_38])).
% 13.69/5.52  tff(c_79, plain, (![A_65]: (k1_xboole_0!=A_65)), inference(splitLeft, [status(thm)], [c_71])).
% 13.69/5.52  tff(c_86, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_79])).
% 13.69/5.52  tff(c_87, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_71])).
% 13.69/5.52  tff(c_163, plain, (![B_89, A_90, D_91]: (r2_hidden(B_89, k2_relat_1('#skF_6'(A_90, B_89))) | ~r2_hidden(D_91, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_158])).
% 13.69/5.52  tff(c_170, plain, (![B_92, A_93, B_94]: (r2_hidden(B_92, k2_relat_1('#skF_6'(A_93, B_92))) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_6, c_163])).
% 13.69/5.52  tff(c_180, plain, (![B_49, A_48, B_94]: (r2_hidden(B_49, k2_relat_1(k1_xboole_0)) | r1_tarski(A_48, B_94) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_61, c_170])).
% 13.69/5.52  tff(c_211, plain, (![A_97, B_98]: (r1_tarski(A_97, B_98) | k1_xboole_0!=A_97)), inference(splitLeft, [status(thm)], [c_180])).
% 13.69/5.52  tff(c_40, plain, (![C_56]: (~r1_tarski(k2_relat_1(C_56), '#skF_7') | k1_relat_1(C_56)!='#skF_8' | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.69/5.52  tff(c_216, plain, (![C_99]: (k1_relat_1(C_99)!='#skF_8' | ~v1_funct_1(C_99) | ~v1_relat_1(C_99) | k2_relat_1(C_99)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_211, c_40])).
% 13.69/5.52  tff(c_219, plain, (k1_relat_1(k1_xboole_0)!='#skF_8' | ~v1_funct_1(k1_xboole_0) | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_87, c_216])).
% 13.69/5.52  tff(c_225, plain, (k1_xboole_0!='#skF_8' | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_100, c_111, c_219])).
% 13.69/5.52  tff(c_229, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_225])).
% 13.69/5.52  tff(c_62, plain, (![B_49]: ('#skF_6'(k1_xboole_0, B_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_59])).
% 13.69/5.52  tff(c_323, plain, (![A_129, B_130]: (r2_hidden('#skF_3'(A_129, B_130), k1_relat_1(A_129)) | r2_hidden('#skF_4'(A_129, B_130), B_130) | k2_relat_1(A_129)=B_130 | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_338, plain, (![A_48, B_49, B_130]: (r2_hidden('#skF_3'('#skF_6'(A_48, B_49), B_130), A_48) | r2_hidden('#skF_4'('#skF_6'(A_48, B_49), B_130), B_130) | k2_relat_1('#skF_6'(A_48, B_49))=B_130 | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_323])).
% 13.69/5.52  tff(c_11107, plain, (![A_2798, B_2799, B_2800]: (r2_hidden('#skF_3'('#skF_6'(A_2798, B_2799), B_2800), A_2798) | r2_hidden('#skF_4'('#skF_6'(A_2798, B_2799), B_2800), B_2800) | k2_relat_1('#skF_6'(A_2798, B_2799))=B_2800)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_338])).
% 13.69/5.52  tff(c_14, plain, (![A_8, D_47]: (r2_hidden(k1_funct_1(A_8, D_47), k2_relat_1(A_8)) | ~r2_hidden(D_47, k1_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_10759, plain, (![A_2781, B_2782, C_2783]: (r2_hidden('#skF_5'('#skF_6'(A_2781, B_2782), k2_relat_1('#skF_6'(A_2781, B_2782)), C_2783), A_2781) | ~r2_hidden(C_2783, k2_relat_1('#skF_6'(A_2781, B_2782))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_244])).
% 13.69/5.52  tff(c_576, plain, (![B_49, A_165, B_166]: (r2_hidden(B_49, k2_relat_1(k1_xboole_0)) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165) | r1_tarski(k2_relat_1(A_165), B_166) | k1_relat_1(A_165)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_549])).
% 13.69/5.52  tff(c_10392, plain, (![A_165, B_166]: (~v1_funct_1(A_165) | ~v1_relat_1(A_165) | r1_tarski(k2_relat_1(A_165), B_166) | k1_relat_1(A_165)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_576])).
% 13.69/5.52  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.69/5.52  tff(c_10502, plain, (![A_2757, D_2758, B_2759]: (r2_hidden(k1_funct_1(A_2757, D_2758), B_2759) | ~r1_tarski(k2_relat_1(A_2757), B_2759) | ~r2_hidden(D_2758, k1_relat_1(A_2757)) | ~v1_funct_1(A_2757) | ~v1_relat_1(A_2757))), inference(resolution, [status(thm)], [c_151, c_2])).
% 13.69/5.52  tff(c_10525, plain, (![B_49, B_2759, A_48, D_54]: (r2_hidden(B_49, B_2759) | ~r1_tarski(k2_relat_1('#skF_6'(A_48, B_49)), B_2759) | ~r2_hidden(D_54, k1_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | ~r2_hidden(D_54, A_48))), inference(superposition, [status(thm), theory('equality')], [c_32, c_10502])).
% 13.69/5.52  tff(c_10534, plain, (![B_2760, B_2761, A_2762, D_2763]: (r2_hidden(B_2760, B_2761) | ~r1_tarski(k2_relat_1('#skF_6'(A_2762, B_2760)), B_2761) | ~r2_hidden(D_2763, A_2762))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_10525])).
% 13.69/5.52  tff(c_10540, plain, (![B_2760, B_166, D_2763, A_2762]: (r2_hidden(B_2760, B_166) | ~r2_hidden(D_2763, A_2762) | ~v1_funct_1('#skF_6'(A_2762, B_2760)) | ~v1_relat_1('#skF_6'(A_2762, B_2760)) | k1_relat_1('#skF_6'(A_2762, B_2760))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10392, c_10534])).
% 13.69/5.52  tff(c_10565, plain, (![B_2760, B_166, D_2763, A_2762]: (r2_hidden(B_2760, B_166) | ~r2_hidden(D_2763, A_2762) | k1_xboole_0!=A_2762)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38, c_36, c_10540])).
% 13.69/5.52  tff(c_10577, plain, (![D_2763, A_2762]: (~r2_hidden(D_2763, A_2762) | k1_xboole_0!=A_2762)), inference(splitLeft, [status(thm)], [c_10565])).
% 13.69/5.52  tff(c_10791, plain, (![A_2784, C_2785, B_2786]: (k1_xboole_0!=A_2784 | ~r2_hidden(C_2785, k2_relat_1('#skF_6'(A_2784, B_2786))))), inference(resolution, [status(thm)], [c_10759, c_10577])).
% 13.69/5.52  tff(c_10852, plain, (![A_48, C_2785]: (k1_xboole_0!=A_48 | ~r2_hidden(C_2785, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_61, c_10791])).
% 13.69/5.52  tff(c_10872, plain, (![A_48]: (k1_xboole_0!=A_48 | k1_xboole_0!=A_48)), inference(splitLeft, [status(thm)], [c_10852])).
% 13.69/5.52  tff(c_10878, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_10872])).
% 13.69/5.52  tff(c_10944, plain, (![C_2792]: (~r2_hidden(C_2792, k2_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_10852])).
% 13.69/5.52  tff(c_10966, plain, (![D_47]: (~r2_hidden(D_47, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_10944])).
% 13.69/5.52  tff(c_10977, plain, (![D_47]: (~r2_hidden(D_47, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_100, c_111, c_10966])).
% 13.69/5.52  tff(c_11115, plain, (![B_2799, B_2800]: (r2_hidden('#skF_4'('#skF_6'(k1_xboole_0, B_2799), B_2800), B_2800) | k2_relat_1('#skF_6'(k1_xboole_0, B_2799))=B_2800)), inference(resolution, [status(thm)], [c_11107, c_10977])).
% 13.69/5.52  tff(c_11246, plain, (![B_2803]: (r2_hidden('#skF_4'(k1_xboole_0, B_2803), B_2803) | k2_relat_1(k1_xboole_0)=B_2803)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_11115])).
% 13.69/5.52  tff(c_11254, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_11246, c_10977])).
% 13.69/5.52  tff(c_11284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_11254])).
% 13.69/5.52  tff(c_11285, plain, (![B_2760, B_166]: (r2_hidden(B_2760, B_166))), inference(splitRight, [status(thm)], [c_10565])).
% 13.69/5.52  tff(c_130, plain, (![A_79, B_80, D_81]: (k1_funct_1('#skF_6'(A_79, B_80), D_81)=B_80 | ~r2_hidden(D_81, A_79))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.69/5.52  tff(c_139, plain, (![D_81, B_49, A_48]: (k1_funct_1(k1_xboole_0, D_81)=B_49 | ~r2_hidden(D_81, A_48) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_61, c_130])).
% 13.69/5.52  tff(c_11334, plain, (![D_81, B_49, A_48]: (k1_funct_1(k1_xboole_0, D_81)=B_49 | k1_xboole_0!=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_11285, c_139])).
% 13.69/5.52  tff(c_11356, plain, (![A_48]: (k1_xboole_0!=A_48)), inference(splitLeft, [status(thm)], [c_11334])).
% 13.69/5.52  tff(c_11364, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_11356])).
% 13.69/5.52  tff(c_11381, plain, (![D_2808]: (k1_funct_1(k1_xboole_0, D_2808)='#skF_8')), inference(splitRight, [status(thm)], [c_11334])).
% 13.69/5.52  tff(c_11365, plain, (![D_81, B_49]: (k1_funct_1(k1_xboole_0, D_81)=B_49)), inference(splitRight, [status(thm)], [c_11334])).
% 13.69/5.52  tff(c_11495, plain, (![B_3167]: (B_3167='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_11381, c_11365])).
% 13.69/5.52  tff(c_620, plain, (![A_168, B_169, B_167]: (k1_relat_1('#skF_6'(A_168, B_169))!='#skF_8' | ~v1_funct_1('#skF_6'(A_168, B_169)) | ~v1_relat_1('#skF_6'(A_168, B_169)) | r2_hidden(B_167, k2_relat_1('#skF_6'(A_168, B_167))))), inference(resolution, [status(thm)], [c_596, c_40])).
% 13.69/5.52  tff(c_643, plain, (![A_171, B_172]: (A_171!='#skF_8' | r2_hidden(B_172, k2_relat_1('#skF_6'(A_171, B_172))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_620])).
% 13.69/5.52  tff(c_656, plain, (![A_48, B_49]: (A_48!='#skF_8' | r2_hidden(B_49, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_61, c_643])).
% 13.69/5.52  tff(c_664, plain, (![A_48]: (A_48!='#skF_8' | k1_xboole_0!=A_48)), inference(splitLeft, [status(thm)], [c_656])).
% 13.69/5.52  tff(c_668, plain, (k1_xboole_0!='#skF_8'), inference(reflexivity, [status(thm), theory('equality')], [c_664])).
% 13.69/5.52  tff(c_11543, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_11495, c_668])).
% 13.69/5.52  tff(c_11545, plain, (![B_3559]: (r2_hidden(B_3559, k2_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_576])).
% 13.69/5.52  tff(c_11562, plain, (![B_3559, B_2]: (r2_hidden(B_3559, B_2) | ~r1_tarski(k2_relat_1(k1_xboole_0), B_2))), inference(resolution, [status(thm)], [c_11545, c_2])).
% 13.69/5.52  tff(c_11578, plain, (![B_3559, B_2]: (r2_hidden(B_3559, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_10088, c_11562])).
% 13.69/5.52  tff(c_11624, plain, (![D_81, B_49, A_48]: (k1_funct_1(k1_xboole_0, D_81)=B_49 | k1_xboole_0!=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_11578, c_139])).
% 13.69/5.52  tff(c_11659, plain, (![A_48]: (k1_xboole_0!=A_48)), inference(splitLeft, [status(thm)], [c_11624])).
% 13.69/5.52  tff(c_11667, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_11659])).
% 13.69/5.52  tff(c_11674, plain, (![D_3567]: (k1_funct_1(k1_xboole_0, D_3567)='#skF_8')), inference(splitRight, [status(thm)], [c_11624])).
% 13.69/5.52  tff(c_11668, plain, (![D_81, B_49]: (k1_funct_1(k1_xboole_0, D_81)=B_49)), inference(splitRight, [status(thm)], [c_11624])).
% 13.69/5.52  tff(c_11814, plain, (![B_3943]: (B_3943='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_11674, c_11668])).
% 13.69/5.52  tff(c_11866, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_11814, c_668])).
% 13.69/5.52  tff(c_11867, plain, (![B_49]: (r2_hidden(B_49, k2_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_656])).
% 13.69/5.52  tff(c_12742, plain, (![C_4464, B_4465, A_4466]: (C_4464=B_4465 | ~r2_hidden('#skF_5'('#skF_6'(A_4466, B_4465), k2_relat_1('#skF_6'(A_4466, B_4465)), C_4464), A_4466) | ~r2_hidden(C_4464, k2_relat_1('#skF_6'(A_4466, B_4465))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_195])).
% 13.69/5.52  tff(c_12758, plain, (![C_4467, B_4468, A_4469]: (C_4467=B_4468 | ~r2_hidden(C_4467, k2_relat_1('#skF_6'(A_4469, B_4468))))), inference(resolution, [status(thm)], [c_249, c_12742])).
% 13.69/5.52  tff(c_12831, plain, (![C_4467, B_49, A_48]: (C_4467=B_49 | ~r2_hidden(C_4467, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_61, c_12758])).
% 13.69/5.52  tff(c_12870, plain, (![C_4467, B_49, A_48]: (C_4467=B_49 | k1_xboole_0!=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_11867, c_12831])).
% 13.69/5.52  tff(c_12871, plain, (![A_48]: (k1_xboole_0!=A_48)), inference(splitLeft, [status(thm)], [c_12870])).
% 13.69/5.52  tff(c_12879, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_12871])).
% 13.69/5.52  tff(c_12891, plain, (![C_4475, B_4476]: (C_4475=B_4476)), inference(splitRight, [status(thm)], [c_12870])).
% 13.69/5.52  tff(c_20029, plain, (![C_4475]: (k1_xboole_0!=C_4475)), inference(superposition, [status(thm), theory('equality')], [c_12891, c_229])).
% 13.69/5.52  tff(c_20967, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_20029])).
% 13.69/5.52  tff(c_20969, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_225])).
% 13.69/5.52  tff(c_21132, plain, (![A_6684, B_6685]: (r2_hidden('#skF_3'(A_6684, B_6685), k1_relat_1(A_6684)) | r2_hidden('#skF_4'(A_6684, B_6685), B_6685) | k2_relat_1(A_6684)=B_6685 | ~v1_funct_1(A_6684) | ~v1_relat_1(A_6684))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_21149, plain, (![A_48, B_49, B_6685]: (r2_hidden('#skF_3'('#skF_6'(A_48, B_49), B_6685), A_48) | r2_hidden('#skF_4'('#skF_6'(A_48, B_49), B_6685), B_6685) | k2_relat_1('#skF_6'(A_48, B_49))=B_6685 | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_21132])).
% 13.69/5.52  tff(c_22968, plain, (![A_6864, B_6865, B_6866]: (r2_hidden('#skF_3'('#skF_6'(A_6864, B_6865), B_6866), A_6864) | r2_hidden('#skF_4'('#skF_6'(A_6864, B_6865), B_6866), B_6866) | k2_relat_1('#skF_6'(A_6864, B_6865))=B_6866)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_21149])).
% 13.69/5.52  tff(c_20976, plain, (![D_47]: (r2_hidden(k1_funct_1(k1_xboole_0, D_47), k1_xboole_0) | ~r2_hidden(D_47, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20969, c_14])).
% 13.69/5.52  tff(c_21020, plain, (![D_6658]: (r2_hidden(k1_funct_1(k1_xboole_0, D_6658), k1_xboole_0) | ~r2_hidden(D_6658, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_100, c_111, c_20976])).
% 13.69/5.52  tff(c_21022, plain, (![B_49, D_6658]: (r2_hidden(B_49, k2_relat_1('#skF_6'(k1_xboole_0, B_49))) | ~r2_hidden(D_6658, k1_xboole_0))), inference(resolution, [status(thm)], [c_21020, c_162])).
% 13.69/5.52  tff(c_21032, plain, (![B_49, D_6658]: (r2_hidden(B_49, k1_xboole_0) | ~r2_hidden(D_6658, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20969, c_62, c_21022])).
% 13.69/5.52  tff(c_21039, plain, (![D_6658]: (~r2_hidden(D_6658, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_21032])).
% 13.69/5.52  tff(c_22995, plain, (![B_6865, B_6866]: (r2_hidden('#skF_4'('#skF_6'(k1_xboole_0, B_6865), B_6866), B_6866) | k2_relat_1('#skF_6'(k1_xboole_0, B_6865))=B_6866)), inference(resolution, [status(thm)], [c_22968, c_21039])).
% 13.69/5.52  tff(c_23044, plain, (![B_6866]: (r2_hidden('#skF_4'(k1_xboole_0, B_6866), B_6866) | k1_xboole_0=B_6866)), inference(demodulation, [status(thm), theory('equality')], [c_20969, c_62, c_62, c_22995])).
% 13.69/5.52  tff(c_118, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), A_72) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.69/5.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.69/5.52  tff(c_123, plain, (![A_72]: (r1_tarski(A_72, A_72))), inference(resolution, [status(thm)], [c_118, c_4])).
% 13.69/5.52  tff(c_20995, plain, (![A_6655, C_6656]: (r2_hidden('#skF_5'(A_6655, k2_relat_1(A_6655), C_6656), k1_relat_1(A_6655)) | ~r2_hidden(C_6656, k2_relat_1(A_6655)) | ~v1_funct_1(A_6655) | ~v1_relat_1(A_6655))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_21010, plain, (![A_6655, C_6656, B_2]: (r2_hidden('#skF_5'(A_6655, k2_relat_1(A_6655), C_6656), B_2) | ~r1_tarski(k1_relat_1(A_6655), B_2) | ~r2_hidden(C_6656, k2_relat_1(A_6655)) | ~v1_funct_1(A_6655) | ~v1_relat_1(A_6655))), inference(resolution, [status(thm)], [c_20995, c_2])).
% 13.69/5.52  tff(c_202, plain, (![C_96, B_49, A_48]: (C_96=B_49 | ~r2_hidden(C_96, k2_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | ~r2_hidden('#skF_5'('#skF_6'(A_48, B_49), k2_relat_1('#skF_6'(A_48, B_49)), C_96), A_48))), inference(superposition, [status(thm), theory('equality')], [c_32, c_185])).
% 13.69/5.52  tff(c_24776, plain, (![C_6905, B_6906, A_6907]: (C_6905=B_6906 | ~r2_hidden(C_6905, k2_relat_1('#skF_6'(A_6907, B_6906))) | ~r2_hidden('#skF_5'('#skF_6'(A_6907, B_6906), k2_relat_1('#skF_6'(A_6907, B_6906)), C_6905), A_6907))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_202])).
% 13.69/5.52  tff(c_24789, plain, (![C_6656, B_6906, B_2]: (C_6656=B_6906 | ~r1_tarski(k1_relat_1('#skF_6'(B_2, B_6906)), B_2) | ~r2_hidden(C_6656, k2_relat_1('#skF_6'(B_2, B_6906))) | ~v1_funct_1('#skF_6'(B_2, B_6906)) | ~v1_relat_1('#skF_6'(B_2, B_6906)))), inference(resolution, [status(thm)], [c_21010, c_24776])).
% 13.69/5.52  tff(c_24808, plain, (![C_6908, B_6909, B_6910]: (C_6908=B_6909 | ~r2_hidden(C_6908, k2_relat_1('#skF_6'(B_6910, B_6909))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_123, c_34, c_24789])).
% 13.69/5.52  tff(c_39407, plain, (![B_9994, B_9995, B_9996]: ('#skF_1'(k2_relat_1('#skF_6'(B_9994, B_9995)), B_9996)=B_9995 | r1_tarski(k2_relat_1('#skF_6'(B_9994, B_9995)), B_9996))), inference(resolution, [status(thm)], [c_6, c_24808])).
% 13.69/5.52  tff(c_39533, plain, (![B_9994, B_9995]: (k1_relat_1('#skF_6'(B_9994, B_9995))!='#skF_8' | ~v1_funct_1('#skF_6'(B_9994, B_9995)) | ~v1_relat_1('#skF_6'(B_9994, B_9995)) | '#skF_1'(k2_relat_1('#skF_6'(B_9994, B_9995)), '#skF_7')=B_9995)), inference(resolution, [status(thm)], [c_39407, c_40])).
% 13.69/5.52  tff(c_39677, plain, (![B_10014, B_10015]: (B_10014!='#skF_8' | '#skF_1'(k2_relat_1('#skF_6'(B_10014, B_10015)), '#skF_7')=B_10015)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_39533])).
% 13.69/5.52  tff(c_39873, plain, (![B_10052, B_10053]: (~r2_hidden(B_10052, '#skF_7') | r1_tarski(k2_relat_1('#skF_6'(B_10053, B_10052)), '#skF_7') | B_10053!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_39677, c_4])).
% 13.69/5.52  tff(c_39912, plain, (![B_10053, B_10052]: (k1_relat_1('#skF_6'(B_10053, B_10052))!='#skF_8' | ~v1_funct_1('#skF_6'(B_10053, B_10052)) | ~v1_relat_1('#skF_6'(B_10053, B_10052)) | ~r2_hidden(B_10052, '#skF_7') | B_10053!='#skF_8')), inference(resolution, [status(thm)], [c_39873, c_40])).
% 13.69/5.52  tff(c_40000, plain, (![B_10052, B_10053]: (~r2_hidden(B_10052, '#skF_7') | B_10053!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_39912])).
% 13.69/5.52  tff(c_40015, plain, (![B_10053]: (B_10053!='#skF_8')), inference(splitLeft, [status(thm)], [c_40000])).
% 13.69/5.52  tff(c_40019, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_40015])).
% 13.69/5.52  tff(c_40022, plain, (![B_10071]: (~r2_hidden(B_10071, '#skF_7'))), inference(splitRight, [status(thm)], [c_40000])).
% 13.69/5.52  tff(c_40046, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_23044, c_40022])).
% 13.69/5.52  tff(c_40082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_40046])).
% 13.69/5.52  tff(c_40086, plain, (![B_10089]: (r2_hidden(B_10089, k1_xboole_0))), inference(splitRight, [status(thm)], [c_21032])).
% 13.69/5.52  tff(c_40251, plain, (![B_10089]: (k1_funct_1(k1_xboole_0, B_10089)='#skF_8')), inference(resolution, [status(thm)], [c_40086, c_139])).
% 13.69/5.52  tff(c_40140, plain, (![B_10097, B_10098]: (k1_funct_1(k1_xboole_0, B_10097)=B_10098)), inference(resolution, [status(thm)], [c_40086, c_139])).
% 13.69/5.52  tff(c_40328, plain, (![B_10747]: (B_10747='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_40251, c_40140])).
% 13.69/5.52  tff(c_20968, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_225])).
% 13.69/5.52  tff(c_40360, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_40328, c_20968])).
% 13.69/5.52  tff(c_40361, plain, (![B_49]: (r2_hidden(B_49, k2_relat_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_180])).
% 13.69/5.52  tff(c_40434, plain, (![A_11078, C_11079]: (r2_hidden('#skF_5'(A_11078, k2_relat_1(A_11078), C_11079), k1_relat_1(A_11078)) | ~r2_hidden(C_11079, k2_relat_1(A_11078)) | ~v1_funct_1(A_11078) | ~v1_relat_1(A_11078))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_40446, plain, (![A_11078, C_11079, B_2]: (r2_hidden('#skF_5'(A_11078, k2_relat_1(A_11078), C_11079), B_2) | ~r1_tarski(k1_relat_1(A_11078), B_2) | ~r2_hidden(C_11079, k2_relat_1(A_11078)) | ~v1_funct_1(A_11078) | ~v1_relat_1(A_11078))), inference(resolution, [status(thm)], [c_40434, c_2])).
% 13.69/5.52  tff(c_40393, plain, (![A_11074, C_11075]: (k1_funct_1(A_11074, '#skF_5'(A_11074, k2_relat_1(A_11074), C_11075))=C_11075 | ~r2_hidden(C_11075, k2_relat_1(A_11074)) | ~v1_funct_1(A_11074) | ~v1_relat_1(A_11074))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_40410, plain, (![C_11075, B_49, A_48]: (C_11075=B_49 | ~r2_hidden(C_11075, k2_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | ~r2_hidden('#skF_5'('#skF_6'(A_48, B_49), k2_relat_1('#skF_6'(A_48, B_49)), C_11075), A_48))), inference(superposition, [status(thm), theory('equality')], [c_32, c_40393])).
% 13.69/5.52  tff(c_41934, plain, (![C_12050, B_12051, A_12052]: (C_12050=B_12051 | ~r2_hidden(C_12050, k2_relat_1('#skF_6'(A_12052, B_12051))) | ~r2_hidden('#skF_5'('#skF_6'(A_12052, B_12051), k2_relat_1('#skF_6'(A_12052, B_12051)), C_12050), A_12052))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_40410])).
% 13.69/5.52  tff(c_41938, plain, (![C_11079, B_12051, B_2]: (C_11079=B_12051 | ~r1_tarski(k1_relat_1('#skF_6'(B_2, B_12051)), B_2) | ~r2_hidden(C_11079, k2_relat_1('#skF_6'(B_2, B_12051))) | ~v1_funct_1('#skF_6'(B_2, B_12051)) | ~v1_relat_1('#skF_6'(B_2, B_12051)))), inference(resolution, [status(thm)], [c_40446, c_41934])).
% 13.69/5.52  tff(c_41957, plain, (![C_12053, B_12054, B_12055]: (C_12053=B_12054 | ~r2_hidden(C_12053, k2_relat_1('#skF_6'(B_12055, B_12054))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_123, c_34, c_41938])).
% 13.69/5.52  tff(c_42030, plain, (![C_12053, B_49, A_48]: (C_12053=B_49 | ~r2_hidden(C_12053, k2_relat_1(k1_xboole_0)) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_61, c_41957])).
% 13.69/5.52  tff(c_42064, plain, (![C_12053, B_49, A_48]: (C_12053=B_49 | k1_xboole_0!=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_40361, c_42030])).
% 13.69/5.52  tff(c_42065, plain, (![A_48]: (k1_xboole_0!=A_48)), inference(splitLeft, [status(thm)], [c_42064])).
% 13.69/5.52  tff(c_42073, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_42065])).
% 13.69/5.52  tff(c_42111, plain, (![C_12060, B_12061]: (C_12060=B_12061)), inference(splitRight, [status(thm)], [c_42064])).
% 13.69/5.52  tff(c_48605, plain, (![B_12061]: (B_12061!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_42111, c_44])).
% 13.69/5.52  tff(c_48791, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_48605])).
% 13.69/5.52  tff(c_48792, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_42])).
% 13.69/5.52  tff(c_12, plain, (![A_7]: (k1_relat_1(A_7)!=k1_xboole_0 | k1_xboole_0=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.69/5.52  tff(c_48825, plain, (![A_14043]: (k1_relat_1(A_14043)!='#skF_8' | A_14043='#skF_8' | ~v1_relat_1(A_14043))), inference(demodulation, [status(thm), theory('equality')], [c_48792, c_48792, c_12])).
% 13.69/5.52  tff(c_48828, plain, (![A_48, B_49]: (k1_relat_1('#skF_6'(A_48, B_49))!='#skF_8' | '#skF_6'(A_48, B_49)='#skF_8')), inference(resolution, [status(thm)], [c_38, c_48825])).
% 13.69/5.52  tff(c_48832, plain, (![A_14044, B_14045]: (A_14044!='#skF_8' | '#skF_6'(A_14044, B_14045)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48828])).
% 13.69/5.52  tff(c_48840, plain, (![A_14044]: (v1_relat_1('#skF_8') | A_14044!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48832, c_38])).
% 13.69/5.52  tff(c_48848, plain, (![A_14044]: (A_14044!='#skF_8')), inference(splitLeft, [status(thm)], [c_48840])).
% 13.69/5.52  tff(c_48793, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_42])).
% 13.69/5.52  tff(c_48800, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48792, c_48793])).
% 13.69/5.52  tff(c_48855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48848, c_48800])).
% 13.69/5.52  tff(c_48856, plain, (v1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_48840])).
% 13.69/5.52  tff(c_48842, plain, (![A_14044]: (v1_funct_1('#skF_8') | A_14044!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48832, c_36])).
% 13.69/5.52  tff(c_48867, plain, (![A_14044]: (A_14044!='#skF_8')), inference(splitLeft, [status(thm)], [c_48842])).
% 13.69/5.52  tff(c_48873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48867, c_48800])).
% 13.69/5.52  tff(c_48874, plain, (v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_48842])).
% 13.69/5.52  tff(c_48876, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_48832, c_34])).
% 13.69/5.52  tff(c_48882, plain, (![A_14050, B_14051]: (r2_hidden('#skF_1'(A_14050, B_14051), A_14050) | r1_tarski(A_14050, B_14051))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.69/5.52  tff(c_48887, plain, (![A_14050]: (r1_tarski(A_14050, A_14050))), inference(resolution, [status(thm)], [c_48882, c_4])).
% 13.69/5.52  tff(c_48830, plain, (![A_48, B_49]: (A_48!='#skF_8' | '#skF_6'(A_48, B_49)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48828])).
% 13.69/5.52  tff(c_49013, plain, (![A_14083, C_14084]: (r2_hidden('#skF_5'(A_14083, k2_relat_1(A_14083), C_14084), k1_relat_1(A_14083)) | ~r2_hidden(C_14084, k2_relat_1(A_14083)) | ~v1_funct_1(A_14083) | ~v1_relat_1(A_14083))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_48927, plain, (![A_14068, D_14069]: (r2_hidden(k1_funct_1(A_14068, D_14069), k2_relat_1(A_14068)) | ~r2_hidden(D_14069, k1_relat_1(A_14068)) | ~v1_funct_1(A_14068) | ~v1_relat_1(A_14068))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_48934, plain, (![B_49, A_48, D_54]: (r2_hidden(B_49, k2_relat_1('#skF_6'(A_48, B_49))) | ~r2_hidden(D_54, k1_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | ~r2_hidden(D_54, A_48))), inference(superposition, [status(thm), theory('equality')], [c_32, c_48927])).
% 13.69/5.52  tff(c_48938, plain, (![B_49, A_48, D_54]: (r2_hidden(B_49, k2_relat_1('#skF_6'(A_48, B_49))) | ~r2_hidden(D_54, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_48934])).
% 13.69/5.52  tff(c_49242, plain, (![B_14133, A_14134, C_14135]: (r2_hidden(B_14133, k2_relat_1('#skF_6'(k1_relat_1(A_14134), B_14133))) | ~r2_hidden(C_14135, k2_relat_1(A_14134)) | ~v1_funct_1(A_14134) | ~v1_relat_1(A_14134))), inference(resolution, [status(thm)], [c_49013, c_48938])).
% 13.69/5.52  tff(c_49311, plain, (![B_14139, A_14140, B_14141]: (r2_hidden(B_14139, k2_relat_1('#skF_6'(k1_relat_1(A_14140), B_14139))) | ~v1_funct_1(A_14140) | ~v1_relat_1(A_14140) | r1_tarski(k2_relat_1(A_14140), B_14141))), inference(resolution, [status(thm)], [c_6, c_49242])).
% 13.69/5.52  tff(c_49341, plain, (![B_14139, A_48, B_49, B_14141]: (r2_hidden(B_14139, k2_relat_1('#skF_6'(A_48, B_14139))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | r1_tarski(k2_relat_1('#skF_6'(A_48, B_49)), B_14141))), inference(superposition, [status(thm), theory('equality')], [c_34, c_49311])).
% 13.69/5.52  tff(c_49358, plain, (![B_14142, A_14143, B_14144, B_14145]: (r2_hidden(B_14142, k2_relat_1('#skF_6'(A_14143, B_14142))) | r1_tarski(k2_relat_1('#skF_6'(A_14143, B_14144)), B_14145))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_49341])).
% 13.69/5.52  tff(c_48801, plain, (![C_56]: (~r1_tarski(k2_relat_1(C_56), '#skF_8') | k1_relat_1(C_56)!='#skF_8' | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(demodulation, [status(thm), theory('equality')], [c_48800, c_40])).
% 13.69/5.52  tff(c_49382, plain, (![A_14143, B_14144, B_14142]: (k1_relat_1('#skF_6'(A_14143, B_14144))!='#skF_8' | ~v1_funct_1('#skF_6'(A_14143, B_14144)) | ~v1_relat_1('#skF_6'(A_14143, B_14144)) | r2_hidden(B_14142, k2_relat_1('#skF_6'(A_14143, B_14142))))), inference(resolution, [status(thm)], [c_49358, c_48801])).
% 13.69/5.52  tff(c_49406, plain, (![A_14149, B_14150]: (A_14149!='#skF_8' | r2_hidden(B_14150, k2_relat_1('#skF_6'(A_14149, B_14150))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_49382])).
% 13.69/5.52  tff(c_49419, plain, (![A_48, B_49]: (A_48!='#skF_8' | r2_hidden(B_49, k2_relat_1('#skF_8')) | A_48!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48830, c_49406])).
% 13.69/5.52  tff(c_49427, plain, (![A_48]: (A_48!='#skF_8' | A_48!='#skF_8')), inference(splitLeft, [status(thm)], [c_49419])).
% 13.69/5.52  tff(c_49433, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_49427])).
% 13.69/5.52  tff(c_49434, plain, (![B_49]: (r2_hidden(B_49, k2_relat_1('#skF_8')))), inference(splitRight, [status(thm)], [c_49419])).
% 13.69/5.52  tff(c_49025, plain, (![A_14083, C_14084, B_2]: (r2_hidden('#skF_5'(A_14083, k2_relat_1(A_14083), C_14084), B_2) | ~r1_tarski(k1_relat_1(A_14083), B_2) | ~r2_hidden(C_14084, k2_relat_1(A_14083)) | ~v1_funct_1(A_14083) | ~v1_relat_1(A_14083))), inference(resolution, [status(thm)], [c_49013, c_2])).
% 13.69/5.52  tff(c_48964, plain, (![A_14076, C_14077]: (k1_funct_1(A_14076, '#skF_5'(A_14076, k2_relat_1(A_14076), C_14077))=C_14077 | ~r2_hidden(C_14077, k2_relat_1(A_14076)) | ~v1_funct_1(A_14076) | ~v1_relat_1(A_14076))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_48981, plain, (![C_14077, B_49, A_48]: (C_14077=B_49 | ~r2_hidden(C_14077, k2_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | ~r2_hidden('#skF_5'('#skF_6'(A_48, B_49), k2_relat_1('#skF_6'(A_48, B_49)), C_14077), A_48))), inference(superposition, [status(thm), theory('equality')], [c_32, c_48964])).
% 13.69/5.52  tff(c_50792, plain, (![C_14305, B_14306, A_14307]: (C_14305=B_14306 | ~r2_hidden(C_14305, k2_relat_1('#skF_6'(A_14307, B_14306))) | ~r2_hidden('#skF_5'('#skF_6'(A_14307, B_14306), k2_relat_1('#skF_6'(A_14307, B_14306)), C_14305), A_14307))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_48981])).
% 13.69/5.52  tff(c_50796, plain, (![C_14084, B_14306, B_2]: (C_14084=B_14306 | ~r1_tarski(k1_relat_1('#skF_6'(B_2, B_14306)), B_2) | ~r2_hidden(C_14084, k2_relat_1('#skF_6'(B_2, B_14306))) | ~v1_funct_1('#skF_6'(B_2, B_14306)) | ~v1_relat_1('#skF_6'(B_2, B_14306)))), inference(resolution, [status(thm)], [c_49025, c_50792])).
% 13.69/5.52  tff(c_50815, plain, (![C_14308, B_14309, B_14310]: (C_14308=B_14309 | ~r2_hidden(C_14308, k2_relat_1('#skF_6'(B_14310, B_14309))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_48887, c_34, c_50796])).
% 13.69/5.52  tff(c_50895, plain, (![C_14308, B_49, A_48]: (C_14308=B_49 | ~r2_hidden(C_14308, k2_relat_1('#skF_8')) | A_48!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48830, c_50815])).
% 13.69/5.52  tff(c_50937, plain, (![C_14308, B_49, A_48]: (C_14308=B_49 | A_48!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_49434, c_50895])).
% 13.69/5.52  tff(c_50938, plain, (![A_48]: (A_48!='#skF_8')), inference(splitLeft, [status(thm)], [c_50937])).
% 13.69/5.52  tff(c_50945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50938, c_48800])).
% 13.69/5.52  tff(c_51013, plain, (![C_14316, B_14317]: (C_14316=B_14317)), inference(splitRight, [status(thm)], [c_50937])).
% 13.69/5.52  tff(c_48939, plain, (![B_14070, A_14071, D_14072]: (r2_hidden(B_14070, k2_relat_1('#skF_6'(A_14071, B_14070))) | ~r2_hidden(D_14072, A_14071))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_48934])).
% 13.69/5.52  tff(c_48949, plain, (![B_14073, A_14074, B_14075]: (r2_hidden(B_14073, k2_relat_1('#skF_6'(A_14074, B_14073))) | r1_tarski(A_14074, B_14075))), inference(resolution, [status(thm)], [c_6, c_48939])).
% 13.69/5.52  tff(c_48959, plain, (![B_49, A_48, B_14075]: (r2_hidden(B_49, k2_relat_1('#skF_8')) | r1_tarski(A_48, B_14075) | A_48!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48830, c_48949])).
% 13.69/5.52  tff(c_48990, plain, (![A_14078, B_14079]: (r1_tarski(A_14078, B_14079) | A_14078!='#skF_8')), inference(splitLeft, [status(thm)], [c_48959])).
% 13.69/5.52  tff(c_48995, plain, (![C_14080]: (k1_relat_1(C_14080)!='#skF_8' | ~v1_funct_1(C_14080) | ~v1_relat_1(C_14080) | k2_relat_1(C_14080)!='#skF_8')), inference(resolution, [status(thm)], [c_48990, c_48801])).
% 13.69/5.52  tff(c_48998, plain, (k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | k2_relat_1('#skF_8')!='#skF_8'), inference(resolution, [status(thm)], [c_48856, c_48995])).
% 13.69/5.52  tff(c_49004, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_48874, c_48876, c_48998])).
% 13.69/5.52  tff(c_59915, plain, (![C_14316]: (C_14316!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_51013, c_49004])).
% 13.69/5.52  tff(c_61062, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_59915])).
% 13.69/5.52  tff(c_61063, plain, (![B_49]: (r2_hidden(B_49, k2_relat_1('#skF_8')))), inference(splitRight, [status(thm)], [c_48959])).
% 13.69/5.52  tff(c_61136, plain, (![A_16807, C_16808]: (r2_hidden('#skF_5'(A_16807, k2_relat_1(A_16807), C_16808), k1_relat_1(A_16807)) | ~r2_hidden(C_16808, k2_relat_1(A_16807)) | ~v1_funct_1(A_16807) | ~v1_relat_1(A_16807))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_61148, plain, (![A_16807, C_16808, B_2]: (r2_hidden('#skF_5'(A_16807, k2_relat_1(A_16807), C_16808), B_2) | ~r1_tarski(k1_relat_1(A_16807), B_2) | ~r2_hidden(C_16808, k2_relat_1(A_16807)) | ~v1_funct_1(A_16807) | ~v1_relat_1(A_16807))), inference(resolution, [status(thm)], [c_61136, c_2])).
% 13.69/5.52  tff(c_61095, plain, (![A_16803, C_16804]: (k1_funct_1(A_16803, '#skF_5'(A_16803, k2_relat_1(A_16803), C_16804))=C_16804 | ~r2_hidden(C_16804, k2_relat_1(A_16803)) | ~v1_funct_1(A_16803) | ~v1_relat_1(A_16803))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.69/5.52  tff(c_61105, plain, (![C_16804, B_49, A_48]: (C_16804=B_49 | ~r2_hidden('#skF_5'('#skF_6'(A_48, B_49), k2_relat_1('#skF_6'(A_48, B_49)), C_16804), A_48) | ~r2_hidden(C_16804, k2_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_61095, c_32])).
% 13.69/5.52  tff(c_62455, plain, (![C_17717, B_17718, A_17719]: (C_17717=B_17718 | ~r2_hidden('#skF_5'('#skF_6'(A_17719, B_17718), k2_relat_1('#skF_6'(A_17719, B_17718)), C_17717), A_17719) | ~r2_hidden(C_17717, k2_relat_1('#skF_6'(A_17719, B_17718))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_61105])).
% 13.69/5.52  tff(c_62459, plain, (![C_16808, B_17718, B_2]: (C_16808=B_17718 | ~r1_tarski(k1_relat_1('#skF_6'(B_2, B_17718)), B_2) | ~r2_hidden(C_16808, k2_relat_1('#skF_6'(B_2, B_17718))) | ~v1_funct_1('#skF_6'(B_2, B_17718)) | ~v1_relat_1('#skF_6'(B_2, B_17718)))), inference(resolution, [status(thm)], [c_61148, c_62455])).
% 13.69/5.52  tff(c_62478, plain, (![C_17720, B_17721, B_17722]: (C_17720=B_17721 | ~r2_hidden(C_17720, k2_relat_1('#skF_6'(B_17722, B_17721))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_48887, c_34, c_62459])).
% 13.69/5.52  tff(c_62537, plain, (![C_17720, B_49, A_48]: (C_17720=B_49 | ~r2_hidden(C_17720, k2_relat_1('#skF_8')) | A_48!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48830, c_62478])).
% 13.69/5.52  tff(c_62565, plain, (![C_17720, B_49, A_48]: (C_17720=B_49 | A_48!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_61063, c_62537])).
% 13.69/5.52  tff(c_62566, plain, (![A_48]: (A_48!='#skF_8')), inference(splitLeft, [status(thm)], [c_62565])).
% 13.69/5.52  tff(c_62573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62566, c_48800])).
% 13.69/5.52  tff(c_62623, plain, (![C_17726, B_17727]: (C_17726=B_17727)), inference(splitRight, [status(thm)], [c_62565])).
% 13.69/5.52  tff(c_61064, plain, (![B_16800]: (r2_hidden(B_16800, k2_relat_1('#skF_8')))), inference(splitRight, [status(thm)], [c_48959])).
% 13.69/5.52  tff(c_48890, plain, (![A_14054, B_14055, D_14056]: (k1_funct_1('#skF_6'(A_14054, B_14055), D_14056)=B_14055 | ~r2_hidden(D_14056, A_14054))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.69/5.52  tff(c_48899, plain, (![D_14056, B_49, A_48]: (k1_funct_1('#skF_8', D_14056)=B_49 | ~r2_hidden(D_14056, A_48) | A_48!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48830, c_48890])).
% 13.69/5.52  tff(c_61076, plain, (![B_16800, B_49]: (k1_funct_1('#skF_8', B_16800)=B_49 | k2_relat_1('#skF_8')!='#skF_8')), inference(resolution, [status(thm)], [c_61064, c_48899])).
% 13.69/5.52  tff(c_61119, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(splitLeft, [status(thm)], [c_61076])).
% 13.69/5.52  tff(c_66435, plain, (![B_17727]: (B_17727!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62623, c_61119])).
% 13.69/5.52  tff(c_68056, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_66435])).
% 13.69/5.52  tff(c_68058, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_61076])).
% 13.69/5.52  tff(c_68072, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_68058, c_48801])).
% 13.69/5.52  tff(c_68081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48856, c_48874, c_48876, c_48887, c_68072])).
% 13.69/5.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.69/5.52  
% 13.69/5.52  Inference rules
% 13.69/5.52  ----------------------
% 13.69/5.52  #Ref     : 23
% 13.69/5.52  #Sup     : 15237
% 13.69/5.52  #Fact    : 4
% 13.69/5.52  #Define  : 0
% 13.69/5.52  #Split   : 41
% 13.69/5.52  #Chain   : 0
% 13.69/5.52  #Close   : 0
% 13.69/5.52  
% 13.69/5.52  Ordering : KBO
% 13.69/5.52  
% 13.69/5.52  Simplification rules
% 13.69/5.52  ----------------------
% 13.69/5.52  #Subsume      : 3466
% 13.69/5.52  #Demod        : 5219
% 13.69/5.52  #Tautology    : 1502
% 13.69/5.52  #SimpNegUnit  : 491
% 13.69/5.52  #BackRed      : 33
% 13.69/5.52  
% 13.69/5.52  #Partial instantiations: 11674
% 13.69/5.52  #Strategies tried      : 1
% 13.69/5.52  
% 13.69/5.52  Timing (in seconds)
% 13.69/5.52  ----------------------
% 13.69/5.52  Preprocessing        : 0.30
% 13.69/5.52  Parsing              : 0.15
% 13.69/5.52  CNF conversion       : 0.03
% 13.69/5.52  Main loop            : 4.41
% 13.69/5.52  Inferencing          : 1.27
% 13.69/5.52  Reduction            : 1.48
% 13.69/5.52  Demodulation         : 1.03
% 13.69/5.52  BG Simplification    : 0.17
% 13.69/5.52  Subsumption          : 1.20
% 13.69/5.52  Abstraction          : 0.23
% 13.69/5.52  MUC search           : 0.00
% 13.69/5.52  Cooper               : 0.00
% 13.69/5.52  Total                : 4.79
% 13.69/5.52  Index Insertion      : 0.00
% 13.69/5.52  Index Deletion       : 0.00
% 13.69/5.52  Index Matching       : 0.00
% 13.69/5.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
