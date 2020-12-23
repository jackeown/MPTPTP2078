%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:59 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 5.65s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 295 expanded)
%              Number of leaves         :   31 ( 117 expanded)
%              Depth                    :   12
%              Number of atoms          :  238 ( 866 expanded)
%              Number of equality atoms :  100 ( 344 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(np__1,type,(
    np__1: $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_93,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_95,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',spc1_boole)).

tff(f_114,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_69,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_50] : k1_relat_1('#skF_8'(A_50)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    ! [A_50] : v1_relat_1('#skF_8'(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_117,plain,(
    ! [A_80] :
      ( k1_relat_1(A_80) != k1_xboole_0
      | k1_xboole_0 = A_80
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_120,plain,(
    ! [A_50] :
      ( k1_relat_1('#skF_8'(A_50)) != k1_xboole_0
      | '#skF_8'(A_50) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_117])).

tff(c_125,plain,(
    ! [A_50] :
      ( k1_xboole_0 != A_50
      | '#skF_8'(A_50) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_120])).

tff(c_221,plain,(
    ! [A_87,C_88] :
      ( k1_funct_1('#skF_8'(A_87),C_88) = k1_xboole_0
      | ~ r2_hidden(C_88,A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_252,plain,(
    ! [C_92,A_93] :
      ( k1_funct_1(k1_xboole_0,C_92) = k1_xboole_0
      | ~ r2_hidden(C_92,A_93)
      | k1_xboole_0 != A_93 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_221])).

tff(c_635,plain,(
    ! [A_123] :
      ( k1_funct_1(k1_xboole_0,'#skF_1'(A_123)) = k1_xboole_0
      | k1_xboole_0 != A_123
      | v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_4,c_252])).

tff(c_54,plain,(
    ! [A_56] : k1_relat_1('#skF_9'(A_56)) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    ! [A_56] : v1_relat_1('#skF_9'(A_56)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_123,plain,(
    ! [A_56] :
      ( k1_relat_1('#skF_9'(A_56)) != k1_xboole_0
      | '#skF_9'(A_56) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_117])).

tff(c_127,plain,(
    ! [A_56] :
      ( k1_xboole_0 != A_56
      | '#skF_9'(A_56) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_123])).

tff(c_239,plain,(
    ! [A_90,C_91] :
      ( k1_funct_1('#skF_9'(A_90),C_91) = np__1
      | ~ r2_hidden(C_91,A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_421,plain,(
    ! [C_102,A_103] :
      ( k1_funct_1(k1_xboole_0,C_102) = np__1
      | ~ r2_hidden(C_102,A_103)
      | k1_xboole_0 != A_103 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_239])).

tff(c_425,plain,(
    ! [A_1] :
      ( k1_funct_1(k1_xboole_0,'#skF_1'(A_1)) = np__1
      | k1_xboole_0 != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_421])).

tff(c_641,plain,(
    ! [A_123] :
      ( np__1 = k1_xboole_0
      | k1_xboole_0 != A_123
      | v1_xboole_0(A_123)
      | k1_xboole_0 != A_123
      | v1_xboole_0(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_425])).

tff(c_667,plain,(
    np__1 = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_641])).

tff(c_60,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_671,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_60])).

tff(c_674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_671])).

tff(c_676,plain,(
    np__1 != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_48,plain,(
    ! [A_50] : v1_funct_1('#skF_8'(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,(
    ! [A_56] : v1_funct_1('#skF_9'(A_56)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_77,plain,(
    ! [C_72,B_73] :
      ( C_72 = B_73
      | k1_relat_1(C_72) != '#skF_10'
      | k1_relat_1(B_73) != '#skF_10'
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72)
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_81,plain,(
    ! [B_73,A_56] :
      ( B_73 = '#skF_9'(A_56)
      | k1_relat_1('#skF_9'(A_56)) != '#skF_10'
      | k1_relat_1(B_73) != '#skF_10'
      | ~ v1_funct_1('#skF_9'(A_56))
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_58,c_77])).

tff(c_87,plain,(
    ! [B_73,A_56] :
      ( B_73 = '#skF_9'(A_56)
      | k1_relat_1('#skF_9'(A_56)) != '#skF_10'
      | k1_relat_1(B_73) != '#skF_10'
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_81])).

tff(c_259,plain,(
    ! [B_94,A_95] :
      ( B_94 = '#skF_9'(A_95)
      | A_95 != '#skF_10'
      | k1_relat_1(B_94) != '#skF_10'
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_87])).

tff(c_263,plain,(
    ! [A_95,A_50] :
      ( '#skF_9'(A_95) = '#skF_8'(A_50)
      | A_95 != '#skF_10'
      | k1_relat_1('#skF_8'(A_50)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_50)) ) ),
    inference(resolution,[status(thm)],[c_50,c_259])).

tff(c_271,plain,(
    ! [A_95,A_50] :
      ( '#skF_9'(A_95) = '#skF_8'(A_50)
      | A_95 != '#skF_10'
      | A_50 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_263])).

tff(c_52,plain,(
    ! [A_56,C_61] :
      ( k1_funct_1('#skF_9'(A_56),C_61) = np__1
      | ~ r2_hidden(C_61,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_757,plain,(
    ! [A_135,D_136] :
      ( r2_hidden(k1_funct_1(A_135,D_136),k2_relat_1(A_135))
      | ~ r2_hidden(D_136,k1_relat_1(A_135))
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_769,plain,(
    ! [A_56,C_61] :
      ( r2_hidden(np__1,k2_relat_1('#skF_9'(A_56)))
      | ~ r2_hidden(C_61,k1_relat_1('#skF_9'(A_56)))
      | ~ v1_funct_1('#skF_9'(A_56))
      | ~ v1_relat_1('#skF_9'(A_56))
      | ~ r2_hidden(C_61,A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_757])).

tff(c_785,plain,(
    ! [A_137,C_138] :
      ( r2_hidden(np__1,k2_relat_1('#skF_9'(A_137)))
      | ~ r2_hidden(C_138,A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_769])).

tff(c_807,plain,(
    ! [A_139] :
      ( r2_hidden(np__1,k2_relat_1('#skF_9'(A_139)))
      | v1_xboole_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_4,c_785])).

tff(c_827,plain,(
    ! [A_50,A_95] :
      ( r2_hidden(np__1,k2_relat_1('#skF_8'(A_50)))
      | v1_xboole_0(A_95)
      | A_95 != '#skF_10'
      | A_50 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_807])).

tff(c_5383,plain,(
    ! [A_50] :
      ( r2_hidden(np__1,k2_relat_1('#skF_8'(A_50)))
      | A_50 != '#skF_10' ) ),
    inference(splitLeft,[status(thm)],[c_827])).

tff(c_967,plain,(
    ! [A_147,C_148] :
      ( r2_hidden('#skF_7'(A_147,k2_relat_1(A_147),C_148),k1_relat_1(A_147))
      | ~ r2_hidden(C_148,k2_relat_1(A_147))
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_986,plain,(
    ! [A_50,C_148] :
      ( r2_hidden('#skF_7'('#skF_8'(A_50),k2_relat_1('#skF_8'(A_50)),C_148),A_50)
      | ~ r2_hidden(C_148,k2_relat_1('#skF_8'(A_50)))
      | ~ v1_funct_1('#skF_8'(A_50))
      | ~ v1_relat_1('#skF_8'(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_967])).

tff(c_1001,plain,(
    ! [A_50,C_148] :
      ( r2_hidden('#skF_7'('#skF_8'(A_50),k2_relat_1('#skF_8'(A_50)),C_148),A_50)
      | ~ r2_hidden(C_148,k2_relat_1('#skF_8'(A_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_986])).

tff(c_1157,plain,(
    ! [A_155,C_156] :
      ( k1_funct_1(A_155,'#skF_7'(A_155,k2_relat_1(A_155),C_156)) = C_156
      | ~ r2_hidden(C_156,k2_relat_1(A_155))
      | ~ v1_funct_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    ! [A_50,C_55] :
      ( k1_funct_1('#skF_8'(A_50),C_55) = k1_xboole_0
      | ~ r2_hidden(C_55,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1171,plain,(
    ! [C_156,A_50] :
      ( k1_xboole_0 = C_156
      | ~ r2_hidden('#skF_7'('#skF_8'(A_50),k2_relat_1('#skF_8'(A_50)),C_156),A_50)
      | ~ r2_hidden(C_156,k2_relat_1('#skF_8'(A_50)))
      | ~ v1_funct_1('#skF_8'(A_50))
      | ~ v1_relat_1('#skF_8'(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_44])).

tff(c_5907,plain,(
    ! [C_267,A_268] :
      ( k1_xboole_0 = C_267
      | ~ r2_hidden('#skF_7'('#skF_8'(A_268),k2_relat_1('#skF_8'(A_268)),C_267),A_268)
      | ~ r2_hidden(C_267,k2_relat_1('#skF_8'(A_268))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1171])).

tff(c_5995,plain,(
    ! [C_271,A_272] :
      ( k1_xboole_0 = C_271
      | ~ r2_hidden(C_271,k2_relat_1('#skF_8'(A_272))) ) ),
    inference(resolution,[status(thm)],[c_1001,c_5907])).

tff(c_5998,plain,(
    ! [A_50] :
      ( np__1 = k1_xboole_0
      | A_50 != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_5383,c_5995])).

tff(c_6097,plain,(
    ! [A_50] : A_50 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_676,c_5998])).

tff(c_6135,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6097])).

tff(c_6138,plain,(
    ! [A_273] :
      ( v1_xboole_0(A_273)
      | A_273 != '#skF_10' ) ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2383,plain,(
    ! [A_210,C_211] :
      ( ~ v1_xboole_0(k1_relat_1(A_210))
      | ~ r2_hidden(C_211,k2_relat_1(A_210))
      | ~ v1_funct_1(A_210)
      | ~ v1_relat_1(A_210) ) ),
    inference(resolution,[status(thm)],[c_967,c_2])).

tff(c_2520,plain,(
    ! [A_212] :
      ( ~ v1_xboole_0(k1_relat_1(A_212))
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212)
      | v1_xboole_0(k2_relat_1(A_212)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2383])).

tff(c_79,plain,(
    ! [B_73,A_50] :
      ( B_73 = '#skF_8'(A_50)
      | k1_relat_1('#skF_8'(A_50)) != '#skF_10'
      | k1_relat_1(B_73) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_50))
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_84,plain,(
    ! [B_73,A_50] :
      ( B_73 = '#skF_8'(A_50)
      | k1_relat_1('#skF_8'(A_50)) != '#skF_10'
      | k1_relat_1(B_73) != '#skF_10'
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_79])).

tff(c_476,plain,(
    ! [B_111,A_112] :
      ( B_111 = '#skF_8'(A_112)
      | A_112 != '#skF_10'
      | k1_relat_1(B_111) != '#skF_10'
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_84])).

tff(c_480,plain,(
    ! [A_50,A_112] :
      ( '#skF_8'(A_50) = '#skF_8'(A_112)
      | A_112 != '#skF_10'
      | k1_relat_1('#skF_8'(A_50)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_50)) ) ),
    inference(resolution,[status(thm)],[c_50,c_476])).

tff(c_488,plain,(
    ! [A_50,A_112] :
      ( '#skF_8'(A_50) = '#skF_8'(A_112)
      | A_112 != '#skF_10'
      | A_50 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_480])).

tff(c_772,plain,(
    ! [A_50,C_55] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_8'(A_50)))
      | ~ r2_hidden(C_55,k1_relat_1('#skF_8'(A_50)))
      | ~ v1_funct_1('#skF_8'(A_50))
      | ~ v1_relat_1('#skF_8'(A_50))
      | ~ r2_hidden(C_55,A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_757])).

tff(c_891,plain,(
    ! [A_143,C_144] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_8'(A_143)))
      | ~ r2_hidden(C_144,A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_772])).

tff(c_916,plain,(
    ! [A_145] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_8'(A_145)))
      | v1_xboole_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_4,c_891])).

tff(c_948,plain,(
    ! [A_146] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_8'(A_146)))
      | v1_xboole_0(A_146) ) ),
    inference(resolution,[status(thm)],[c_916,c_2])).

tff(c_954,plain,(
    ! [A_50,A_112] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_8'(A_50)))
      | v1_xboole_0(A_112)
      | A_112 != '#skF_10'
      | A_50 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_948])).

tff(c_1265,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_8'(A_50)))
      | A_50 != '#skF_10' ) ),
    inference(splitLeft,[status(thm)],[c_954])).

tff(c_2551,plain,(
    ! [A_50] :
      ( A_50 != '#skF_10'
      | ~ v1_xboole_0(k1_relat_1('#skF_8'(A_50)))
      | ~ v1_funct_1('#skF_8'(A_50))
      | ~ v1_relat_1('#skF_8'(A_50)) ) ),
    inference(resolution,[status(thm)],[c_2520,c_1265])).

tff(c_2608,plain,(
    ! [A_50] :
      ( A_50 != '#skF_10'
      | ~ v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_2551])).

tff(c_6221,plain,(
    ! [A_273] : A_273 != '#skF_10' ),
    inference(resolution,[status(thm)],[c_6138,c_2608])).

tff(c_6246,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6221])).

tff(c_6273,plain,(
    ! [A_276] :
      ( v1_xboole_0(A_276)
      | A_276 != '#skF_10' ) ),
    inference(splitRight,[status(thm)],[c_954])).

tff(c_426,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_2'(A_104,B_105),B_105)
      | r2_hidden('#skF_3'(A_104,B_105),A_104)
      | B_105 = A_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_451,plain,(
    ! [B_106,A_107] :
      ( ~ v1_xboole_0(B_106)
      | r2_hidden('#skF_3'(A_107,B_106),A_107)
      | B_106 = A_107 ) ),
    inference(resolution,[status(thm)],[c_426,c_2])).

tff(c_464,plain,(
    ! [A_108,B_109] :
      ( ~ v1_xboole_0(A_108)
      | ~ v1_xboole_0(B_109)
      | B_109 = A_108 ) ),
    inference(resolution,[status(thm)],[c_451,c_2])).

tff(c_467,plain,(
    ! [B_109] :
      ( ~ v1_xboole_0(B_109)
      | k1_xboole_0 = B_109 ) ),
    inference(resolution,[status(thm)],[c_6,c_464])).

tff(c_6312,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6273,c_467])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6312,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.65/2.11  
% 5.65/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.65/2.11  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_1 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_5 > #skF_4
% 5.65/2.11  
% 5.65/2.11  %Foreground sorts:
% 5.65/2.11  
% 5.65/2.11  
% 5.65/2.11  %Background operators:
% 5.65/2.11  
% 5.65/2.11  
% 5.65/2.11  %Foreground operators:
% 5.65/2.11  tff('#skF_9', type, '#skF_9': $i > $i).
% 5.65/2.11  tff(np__1, type, np__1: $i).
% 5.65/2.11  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.65/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.65/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.65/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.65/2.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.65/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.65/2.11  tff('#skF_8', type, '#skF_8': $i > $i).
% 5.65/2.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.65/2.11  tff('#skF_10', type, '#skF_10': $i).
% 5.65/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.65/2.11  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.65/2.11  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.65/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.65/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.65/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.65/2.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.65/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.65/2.11  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.65/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.65/2.11  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.65/2.11  
% 5.65/2.13  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.65/2.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.65/2.13  tff(f_81, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 5.65/2.13  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.65/2.13  tff(f_93, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 5.65/2.13  tff(f_95, axiom, ~v1_xboole_0(np__1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', spc1_boole)).
% 5.65/2.13  tff(f_114, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 5.65/2.13  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 5.65/2.13  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 5.65/2.13  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/2.13  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.65/2.13  tff(c_46, plain, (![A_50]: (k1_relat_1('#skF_8'(A_50))=A_50)), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.65/2.13  tff(c_50, plain, (![A_50]: (v1_relat_1('#skF_8'(A_50)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.65/2.13  tff(c_117, plain, (![A_80]: (k1_relat_1(A_80)!=k1_xboole_0 | k1_xboole_0=A_80 | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.65/2.13  tff(c_120, plain, (![A_50]: (k1_relat_1('#skF_8'(A_50))!=k1_xboole_0 | '#skF_8'(A_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_117])).
% 5.65/2.13  tff(c_125, plain, (![A_50]: (k1_xboole_0!=A_50 | '#skF_8'(A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_120])).
% 5.65/2.13  tff(c_221, plain, (![A_87, C_88]: (k1_funct_1('#skF_8'(A_87), C_88)=k1_xboole_0 | ~r2_hidden(C_88, A_87))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.65/2.13  tff(c_252, plain, (![C_92, A_93]: (k1_funct_1(k1_xboole_0, C_92)=k1_xboole_0 | ~r2_hidden(C_92, A_93) | k1_xboole_0!=A_93)), inference(superposition, [status(thm), theory('equality')], [c_125, c_221])).
% 5.65/2.13  tff(c_635, plain, (![A_123]: (k1_funct_1(k1_xboole_0, '#skF_1'(A_123))=k1_xboole_0 | k1_xboole_0!=A_123 | v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_4, c_252])).
% 5.65/2.13  tff(c_54, plain, (![A_56]: (k1_relat_1('#skF_9'(A_56))=A_56)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.65/2.13  tff(c_58, plain, (![A_56]: (v1_relat_1('#skF_9'(A_56)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.65/2.13  tff(c_123, plain, (![A_56]: (k1_relat_1('#skF_9'(A_56))!=k1_xboole_0 | '#skF_9'(A_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_117])).
% 5.65/2.13  tff(c_127, plain, (![A_56]: (k1_xboole_0!=A_56 | '#skF_9'(A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_123])).
% 5.65/2.13  tff(c_239, plain, (![A_90, C_91]: (k1_funct_1('#skF_9'(A_90), C_91)=np__1 | ~r2_hidden(C_91, A_90))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.65/2.13  tff(c_421, plain, (![C_102, A_103]: (k1_funct_1(k1_xboole_0, C_102)=np__1 | ~r2_hidden(C_102, A_103) | k1_xboole_0!=A_103)), inference(superposition, [status(thm), theory('equality')], [c_127, c_239])).
% 5.65/2.13  tff(c_425, plain, (![A_1]: (k1_funct_1(k1_xboole_0, '#skF_1'(A_1))=np__1 | k1_xboole_0!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_421])).
% 5.65/2.13  tff(c_641, plain, (![A_123]: (np__1=k1_xboole_0 | k1_xboole_0!=A_123 | v1_xboole_0(A_123) | k1_xboole_0!=A_123 | v1_xboole_0(A_123))), inference(superposition, [status(thm), theory('equality')], [c_635, c_425])).
% 5.65/2.13  tff(c_667, plain, (np__1=k1_xboole_0), inference(splitLeft, [status(thm)], [c_641])).
% 5.65/2.13  tff(c_60, plain, (~v1_xboole_0(np__1)), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.65/2.13  tff(c_671, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_667, c_60])).
% 5.65/2.13  tff(c_674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_671])).
% 5.65/2.13  tff(c_676, plain, (np__1!=k1_xboole_0), inference(splitRight, [status(thm)], [c_641])).
% 5.65/2.13  tff(c_48, plain, (![A_50]: (v1_funct_1('#skF_8'(A_50)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.65/2.13  tff(c_56, plain, (![A_56]: (v1_funct_1('#skF_9'(A_56)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.65/2.13  tff(c_77, plain, (![C_72, B_73]: (C_72=B_73 | k1_relat_1(C_72)!='#skF_10' | k1_relat_1(B_73)!='#skF_10' | ~v1_funct_1(C_72) | ~v1_relat_1(C_72) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.65/2.13  tff(c_81, plain, (![B_73, A_56]: (B_73='#skF_9'(A_56) | k1_relat_1('#skF_9'(A_56))!='#skF_10' | k1_relat_1(B_73)!='#skF_10' | ~v1_funct_1('#skF_9'(A_56)) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_58, c_77])).
% 5.65/2.13  tff(c_87, plain, (![B_73, A_56]: (B_73='#skF_9'(A_56) | k1_relat_1('#skF_9'(A_56))!='#skF_10' | k1_relat_1(B_73)!='#skF_10' | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_81])).
% 5.65/2.13  tff(c_259, plain, (![B_94, A_95]: (B_94='#skF_9'(A_95) | A_95!='#skF_10' | k1_relat_1(B_94)!='#skF_10' | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_87])).
% 5.65/2.13  tff(c_263, plain, (![A_95, A_50]: ('#skF_9'(A_95)='#skF_8'(A_50) | A_95!='#skF_10' | k1_relat_1('#skF_8'(A_50))!='#skF_10' | ~v1_funct_1('#skF_8'(A_50)))), inference(resolution, [status(thm)], [c_50, c_259])).
% 5.65/2.13  tff(c_271, plain, (![A_95, A_50]: ('#skF_9'(A_95)='#skF_8'(A_50) | A_95!='#skF_10' | A_50!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_263])).
% 5.65/2.13  tff(c_52, plain, (![A_56, C_61]: (k1_funct_1('#skF_9'(A_56), C_61)=np__1 | ~r2_hidden(C_61, A_56))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.65/2.13  tff(c_757, plain, (![A_135, D_136]: (r2_hidden(k1_funct_1(A_135, D_136), k2_relat_1(A_135)) | ~r2_hidden(D_136, k1_relat_1(A_135)) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.65/2.13  tff(c_769, plain, (![A_56, C_61]: (r2_hidden(np__1, k2_relat_1('#skF_9'(A_56))) | ~r2_hidden(C_61, k1_relat_1('#skF_9'(A_56))) | ~v1_funct_1('#skF_9'(A_56)) | ~v1_relat_1('#skF_9'(A_56)) | ~r2_hidden(C_61, A_56))), inference(superposition, [status(thm), theory('equality')], [c_52, c_757])).
% 5.65/2.13  tff(c_785, plain, (![A_137, C_138]: (r2_hidden(np__1, k2_relat_1('#skF_9'(A_137))) | ~r2_hidden(C_138, A_137))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_769])).
% 5.65/2.13  tff(c_807, plain, (![A_139]: (r2_hidden(np__1, k2_relat_1('#skF_9'(A_139))) | v1_xboole_0(A_139))), inference(resolution, [status(thm)], [c_4, c_785])).
% 5.65/2.13  tff(c_827, plain, (![A_50, A_95]: (r2_hidden(np__1, k2_relat_1('#skF_8'(A_50))) | v1_xboole_0(A_95) | A_95!='#skF_10' | A_50!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_271, c_807])).
% 5.65/2.13  tff(c_5383, plain, (![A_50]: (r2_hidden(np__1, k2_relat_1('#skF_8'(A_50))) | A_50!='#skF_10')), inference(splitLeft, [status(thm)], [c_827])).
% 5.65/2.13  tff(c_967, plain, (![A_147, C_148]: (r2_hidden('#skF_7'(A_147, k2_relat_1(A_147), C_148), k1_relat_1(A_147)) | ~r2_hidden(C_148, k2_relat_1(A_147)) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.65/2.13  tff(c_986, plain, (![A_50, C_148]: (r2_hidden('#skF_7'('#skF_8'(A_50), k2_relat_1('#skF_8'(A_50)), C_148), A_50) | ~r2_hidden(C_148, k2_relat_1('#skF_8'(A_50))) | ~v1_funct_1('#skF_8'(A_50)) | ~v1_relat_1('#skF_8'(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_967])).
% 5.65/2.13  tff(c_1001, plain, (![A_50, C_148]: (r2_hidden('#skF_7'('#skF_8'(A_50), k2_relat_1('#skF_8'(A_50)), C_148), A_50) | ~r2_hidden(C_148, k2_relat_1('#skF_8'(A_50))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_986])).
% 5.65/2.13  tff(c_1157, plain, (![A_155, C_156]: (k1_funct_1(A_155, '#skF_7'(A_155, k2_relat_1(A_155), C_156))=C_156 | ~r2_hidden(C_156, k2_relat_1(A_155)) | ~v1_funct_1(A_155) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.65/2.13  tff(c_44, plain, (![A_50, C_55]: (k1_funct_1('#skF_8'(A_50), C_55)=k1_xboole_0 | ~r2_hidden(C_55, A_50))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.65/2.13  tff(c_1171, plain, (![C_156, A_50]: (k1_xboole_0=C_156 | ~r2_hidden('#skF_7'('#skF_8'(A_50), k2_relat_1('#skF_8'(A_50)), C_156), A_50) | ~r2_hidden(C_156, k2_relat_1('#skF_8'(A_50))) | ~v1_funct_1('#skF_8'(A_50)) | ~v1_relat_1('#skF_8'(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_1157, c_44])).
% 5.65/2.13  tff(c_5907, plain, (![C_267, A_268]: (k1_xboole_0=C_267 | ~r2_hidden('#skF_7'('#skF_8'(A_268), k2_relat_1('#skF_8'(A_268)), C_267), A_268) | ~r2_hidden(C_267, k2_relat_1('#skF_8'(A_268))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1171])).
% 5.65/2.13  tff(c_5995, plain, (![C_271, A_272]: (k1_xboole_0=C_271 | ~r2_hidden(C_271, k2_relat_1('#skF_8'(A_272))))), inference(resolution, [status(thm)], [c_1001, c_5907])).
% 5.65/2.13  tff(c_5998, plain, (![A_50]: (np__1=k1_xboole_0 | A_50!='#skF_10')), inference(resolution, [status(thm)], [c_5383, c_5995])).
% 5.65/2.13  tff(c_6097, plain, (![A_50]: (A_50!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_676, c_5998])).
% 5.65/2.13  tff(c_6135, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_6097])).
% 5.65/2.13  tff(c_6138, plain, (![A_273]: (v1_xboole_0(A_273) | A_273!='#skF_10')), inference(splitRight, [status(thm)], [c_827])).
% 5.65/2.13  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.65/2.13  tff(c_2383, plain, (![A_210, C_211]: (~v1_xboole_0(k1_relat_1(A_210)) | ~r2_hidden(C_211, k2_relat_1(A_210)) | ~v1_funct_1(A_210) | ~v1_relat_1(A_210))), inference(resolution, [status(thm)], [c_967, c_2])).
% 5.65/2.13  tff(c_2520, plain, (![A_212]: (~v1_xboole_0(k1_relat_1(A_212)) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212) | v1_xboole_0(k2_relat_1(A_212)))), inference(resolution, [status(thm)], [c_4, c_2383])).
% 5.65/2.13  tff(c_79, plain, (![B_73, A_50]: (B_73='#skF_8'(A_50) | k1_relat_1('#skF_8'(A_50))!='#skF_10' | k1_relat_1(B_73)!='#skF_10' | ~v1_funct_1('#skF_8'(A_50)) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_50, c_77])).
% 5.65/2.13  tff(c_84, plain, (![B_73, A_50]: (B_73='#skF_8'(A_50) | k1_relat_1('#skF_8'(A_50))!='#skF_10' | k1_relat_1(B_73)!='#skF_10' | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_79])).
% 5.65/2.13  tff(c_476, plain, (![B_111, A_112]: (B_111='#skF_8'(A_112) | A_112!='#skF_10' | k1_relat_1(B_111)!='#skF_10' | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_84])).
% 5.65/2.13  tff(c_480, plain, (![A_50, A_112]: ('#skF_8'(A_50)='#skF_8'(A_112) | A_112!='#skF_10' | k1_relat_1('#skF_8'(A_50))!='#skF_10' | ~v1_funct_1('#skF_8'(A_50)))), inference(resolution, [status(thm)], [c_50, c_476])).
% 5.65/2.13  tff(c_488, plain, (![A_50, A_112]: ('#skF_8'(A_50)='#skF_8'(A_112) | A_112!='#skF_10' | A_50!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_480])).
% 5.65/2.13  tff(c_772, plain, (![A_50, C_55]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_8'(A_50))) | ~r2_hidden(C_55, k1_relat_1('#skF_8'(A_50))) | ~v1_funct_1('#skF_8'(A_50)) | ~v1_relat_1('#skF_8'(A_50)) | ~r2_hidden(C_55, A_50))), inference(superposition, [status(thm), theory('equality')], [c_44, c_757])).
% 5.65/2.13  tff(c_891, plain, (![A_143, C_144]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_8'(A_143))) | ~r2_hidden(C_144, A_143))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_772])).
% 5.65/2.13  tff(c_916, plain, (![A_145]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_8'(A_145))) | v1_xboole_0(A_145))), inference(resolution, [status(thm)], [c_4, c_891])).
% 5.65/2.13  tff(c_948, plain, (![A_146]: (~v1_xboole_0(k2_relat_1('#skF_8'(A_146))) | v1_xboole_0(A_146))), inference(resolution, [status(thm)], [c_916, c_2])).
% 5.65/2.13  tff(c_954, plain, (![A_50, A_112]: (~v1_xboole_0(k2_relat_1('#skF_8'(A_50))) | v1_xboole_0(A_112) | A_112!='#skF_10' | A_50!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_488, c_948])).
% 5.65/2.13  tff(c_1265, plain, (![A_50]: (~v1_xboole_0(k2_relat_1('#skF_8'(A_50))) | A_50!='#skF_10')), inference(splitLeft, [status(thm)], [c_954])).
% 5.65/2.13  tff(c_2551, plain, (![A_50]: (A_50!='#skF_10' | ~v1_xboole_0(k1_relat_1('#skF_8'(A_50))) | ~v1_funct_1('#skF_8'(A_50)) | ~v1_relat_1('#skF_8'(A_50)))), inference(resolution, [status(thm)], [c_2520, c_1265])).
% 5.65/2.13  tff(c_2608, plain, (![A_50]: (A_50!='#skF_10' | ~v1_xboole_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_2551])).
% 5.65/2.13  tff(c_6221, plain, (![A_273]: (A_273!='#skF_10')), inference(resolution, [status(thm)], [c_6138, c_2608])).
% 5.65/2.13  tff(c_6246, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_6221])).
% 5.65/2.13  tff(c_6273, plain, (![A_276]: (v1_xboole_0(A_276) | A_276!='#skF_10')), inference(splitRight, [status(thm)], [c_954])).
% 5.65/2.13  tff(c_426, plain, (![A_104, B_105]: (r2_hidden('#skF_2'(A_104, B_105), B_105) | r2_hidden('#skF_3'(A_104, B_105), A_104) | B_105=A_104)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.65/2.13  tff(c_451, plain, (![B_106, A_107]: (~v1_xboole_0(B_106) | r2_hidden('#skF_3'(A_107, B_106), A_107) | B_106=A_107)), inference(resolution, [status(thm)], [c_426, c_2])).
% 5.65/2.13  tff(c_464, plain, (![A_108, B_109]: (~v1_xboole_0(A_108) | ~v1_xboole_0(B_109) | B_109=A_108)), inference(resolution, [status(thm)], [c_451, c_2])).
% 5.65/2.13  tff(c_467, plain, (![B_109]: (~v1_xboole_0(B_109) | k1_xboole_0=B_109)), inference(resolution, [status(thm)], [c_6, c_464])).
% 5.65/2.13  tff(c_6312, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_6273, c_467])).
% 5.65/2.13  tff(c_62, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.65/2.13  tff(c_6347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6312, c_62])).
% 5.65/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.65/2.13  
% 5.65/2.13  Inference rules
% 5.65/2.13  ----------------------
% 5.65/2.13  #Ref     : 10
% 5.65/2.13  #Sup     : 1525
% 5.65/2.13  #Fact    : 2
% 5.65/2.13  #Define  : 0
% 5.65/2.13  #Split   : 11
% 5.65/2.13  #Chain   : 0
% 5.65/2.13  #Close   : 0
% 5.65/2.13  
% 5.65/2.13  Ordering : KBO
% 5.65/2.13  
% 5.65/2.13  Simplification rules
% 5.65/2.13  ----------------------
% 5.65/2.13  #Subsume      : 803
% 5.65/2.13  #Demod        : 799
% 5.65/2.13  #Tautology    : 197
% 5.65/2.13  #SimpNegUnit  : 103
% 5.65/2.13  #BackRed      : 39
% 5.65/2.13  
% 5.65/2.13  #Partial instantiations: 0
% 5.65/2.13  #Strategies tried      : 1
% 5.65/2.13  
% 5.65/2.13  Timing (in seconds)
% 5.65/2.13  ----------------------
% 5.96/2.13  Preprocessing        : 0.32
% 5.96/2.13  Parsing              : 0.16
% 5.96/2.13  CNF conversion       : 0.03
% 5.96/2.13  Main loop            : 1.03
% 5.96/2.13  Inferencing          : 0.31
% 5.96/2.13  Reduction            : 0.33
% 5.96/2.13  Demodulation         : 0.22
% 5.96/2.13  BG Simplification    : 0.04
% 5.96/2.13  Subsumption          : 0.27
% 5.96/2.13  Abstraction          : 0.05
% 5.96/2.13  MUC search           : 0.00
% 5.96/2.13  Cooper               : 0.00
% 5.96/2.13  Total                : 1.39
% 5.96/2.13  Index Insertion      : 0.00
% 5.96/2.13  Index Deletion       : 0.00
% 5.96/2.13  Index Matching       : 0.00
% 5.96/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
