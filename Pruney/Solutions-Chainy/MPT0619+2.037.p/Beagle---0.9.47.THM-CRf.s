%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:56 EST 2020

% Result     : Theorem 43.19s
% Output     : CNFRefutation 43.19s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 964 expanded)
%              Number of leaves         :   31 ( 343 expanded)
%              Depth                    :   30
%              Number of atoms          :  221 (2405 expanded)
%              Number of equality atoms :  104 (1198 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_5 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_84,axiom,(
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

tff(c_166,plain,(
    ! [A_70,B_71] :
      ( k2_xboole_0(k1_tarski(A_70),B_71) = B_71
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),B_15) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_180,plain,(
    ! [A_70] : ~ r2_hidden(A_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_24])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    k1_tarski('#skF_9') = k1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_76,plain,(
    ! [C_62,A_63] :
      ( C_62 = A_63
      | ~ r2_hidden(C_62,k1_tarski(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_91,plain,(
    ! [C_65] :
      ( C_65 = '#skF_9'
      | ~ r2_hidden(C_65,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_76])).

tff(c_99,plain,
    ( '#skF_1'(k1_relat_1('#skF_10')) = '#skF_9'
    | k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_91])).

tff(c_120,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_59,plain,(
    ! [C_57] : r2_hidden(C_57,k1_tarski(C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_59])).

tff(c_123,plain,(
    r2_hidden('#skF_9',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_62])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_123])).

tff(c_184,plain,(
    k1_relat_1('#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_54,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_201,plain,(
    ! [A_73] :
      ( k1_relat_1(A_73) = k1_xboole_0
      | k2_relat_1(A_73) != k1_xboole_0
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_204,plain,
    ( k1_relat_1('#skF_10') = k1_xboole_0
    | k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_201])).

tff(c_207,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_204])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_4'(A_11,B_12),A_11)
      | k1_xboole_0 = A_11
      | k1_tarski(B_12) = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    ! [A_17,C_53] :
      ( r2_hidden('#skF_8'(A_17,k2_relat_1(A_17),C_53),k1_relat_1(A_17))
      | ~ r2_hidden(C_53,k2_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    ! [A_17,D_56] :
      ( r2_hidden(k1_funct_1(A_17,D_56),k2_relat_1(A_17))
      | ~ r2_hidden(D_56,k1_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_208,plain,(
    ! [A_74,B_75] :
      ( k2_xboole_0(k1_tarski(A_74),B_75) = B_75
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_222,plain,(
    ! [A_74] : ~ r2_hidden(A_74,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_24])).

tff(c_270,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_4'(A_83,B_84),A_83)
      | k1_xboole_0 = A_83
      | k1_tarski(B_84) = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    ! [C_62] :
      ( C_62 = '#skF_9'
      | ~ r2_hidden(C_62,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_76])).

tff(c_277,plain,(
    ! [B_84] :
      ( '#skF_4'(k1_relat_1('#skF_10'),B_84) = '#skF_9'
      | k1_relat_1('#skF_10') = k1_xboole_0
      | k1_tarski(B_84) = k1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_270,c_82])).

tff(c_289,plain,(
    ! [B_85] :
      ( '#skF_4'(k1_relat_1('#skF_10'),B_85) = '#skF_9'
      | k1_tarski(B_85) = k1_relat_1('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_277])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( '#skF_4'(A_11,B_12) != B_12
      | k1_xboole_0 = A_11
      | k1_tarski(B_12) = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_297,plain,(
    ! [B_85] :
      ( B_85 != '#skF_9'
      | k1_relat_1('#skF_10') = k1_xboole_0
      | k1_tarski(B_85) = k1_relat_1('#skF_10')
      | k1_tarski(B_85) = k1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_20])).

tff(c_304,plain,(
    ! [B_85] :
      ( B_85 != '#skF_9'
      | k1_tarski(B_85) = k1_relat_1('#skF_10')
      | k1_tarski(B_85) = k1_relat_1('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_297])).

tff(c_369,plain,(
    ! [B_89] :
      ( B_89 != '#skF_9'
      | k1_tarski(B_89) = k1_relat_1('#skF_10') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_304])).

tff(c_6,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_401,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_6])).

tff(c_4332,plain,(
    ! [A_6508,B_6509] :
      ( r2_hidden('#skF_6'(A_6508,B_6509),k1_relat_1(A_6508))
      | r2_hidden('#skF_7'(A_6508,B_6509),B_6509)
      | k2_relat_1(A_6508) = B_6509
      | ~ v1_funct_1(A_6508)
      | ~ v1_relat_1(A_6508) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4347,plain,(
    ! [B_6509] :
      ( '#skF_6'('#skF_10',B_6509) = '#skF_9'
      | r2_hidden('#skF_7'('#skF_10',B_6509),B_6509)
      | k2_relat_1('#skF_10') = B_6509
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_4332,c_82])).

tff(c_4450,plain,(
    ! [B_6585] :
      ( '#skF_6'('#skF_10',B_6585) = '#skF_9'
      | r2_hidden('#skF_7'('#skF_10',B_6585),B_6585)
      | k2_relat_1('#skF_10') = B_6585 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4347])).

tff(c_213,plain,(
    ! [B_75,A_74] :
      ( k1_xboole_0 != B_75
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_24])).

tff(c_4671,plain,
    ( '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9'
    | k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4450,c_213])).

tff(c_3833,plain,(
    ! [A_5445,C_5446] :
      ( r2_hidden('#skF_8'(A_5445,k2_relat_1(A_5445),C_5446),k1_relat_1(A_5445))
      | ~ r2_hidden(C_5446,k2_relat_1(A_5445))
      | ~ v1_funct_1(A_5445)
      | ~ v1_relat_1(A_5445) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3848,plain,(
    ! [C_5446] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_5446) = '#skF_9'
      | ~ r2_hidden(C_5446,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_3833,c_82])).

tff(c_3914,plain,(
    ! [C_5522] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_5522) = '#skF_9'
      | ~ r2_hidden(C_5522,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3848])).

tff(c_3936,plain,
    ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),'#skF_1'(k2_relat_1('#skF_10'))) = '#skF_9'
    | k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_3914])).

tff(c_3947,plain,(
    '#skF_8'('#skF_10',k2_relat_1('#skF_10'),'#skF_1'(k2_relat_1('#skF_10'))) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_3936])).

tff(c_32,plain,(
    ! [A_17,C_53] :
      ( k1_funct_1(A_17,'#skF_8'(A_17,k2_relat_1(A_17),C_53)) = C_53
      | ~ r2_hidden(C_53,k2_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3954,plain,
    ( '#skF_1'(k2_relat_1('#skF_10')) = k1_funct_1('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_10')),k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3947,c_32])).

tff(c_3974,plain,
    ( '#skF_1'(k2_relat_1('#skF_10')) = k1_funct_1('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_1'(k2_relat_1('#skF_10')),k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3954])).

tff(c_4048,plain,(
    ~ r2_hidden('#skF_1'(k2_relat_1('#skF_10')),k2_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_3974])).

tff(c_4060,plain,(
    k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_4048])).

tff(c_4064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_4060])).

tff(c_4065,plain,(
    '#skF_1'(k2_relat_1('#skF_10')) = k1_funct_1('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_3974])).

tff(c_4066,plain,(
    r2_hidden('#skF_1'(k2_relat_1('#skF_10')),k2_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_3974])).

tff(c_4139,plain,(
    r2_hidden(k1_funct_1('#skF_10','#skF_9'),k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4065,c_4066])).

tff(c_4672,plain,
    ( r2_hidden(k1_funct_1('#skF_10','#skF_9'),k1_xboole_0)
    | '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_4671,c_4139])).

tff(c_5003,plain,(
    '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_4672])).

tff(c_5142,plain,(
    ! [A_9266,B_9267] :
      ( k1_funct_1(A_9266,'#skF_6'(A_9266,B_9267)) = '#skF_5'(A_9266,B_9267)
      | r2_hidden('#skF_7'(A_9266,B_9267),B_9267)
      | k2_relat_1(A_9266) = B_9267
      | ~ v1_funct_1(A_9266)
      | ~ v1_relat_1(A_9266) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14418,plain,(
    ! [A_22303,B_22304] :
      ( r2_hidden('#skF_5'(A_22303,B_22304),k2_relat_1(A_22303))
      | ~ r2_hidden('#skF_6'(A_22303,B_22304),k1_relat_1(A_22303))
      | ~ v1_funct_1(A_22303)
      | ~ v1_relat_1(A_22303)
      | r2_hidden('#skF_7'(A_22303,B_22304),B_22304)
      | k2_relat_1(A_22303) = B_22304
      | ~ v1_funct_1(A_22303)
      | ~ v1_relat_1(A_22303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5142,c_30])).

tff(c_14442,plain,
    ( r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10'))
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | r2_hidden('#skF_7'('#skF_10',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_10') = k1_xboole_0
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_5003,c_14418])).

tff(c_14506,plain,
    ( r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10'))
    | r2_hidden('#skF_7'('#skF_10',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_54,c_52,c_401,c_14442])).

tff(c_14507,plain,(
    r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_222,c_14506])).

tff(c_3905,plain,(
    ! [C_5446] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_5446) = '#skF_9'
      | ~ r2_hidden(C_5446,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3848])).

tff(c_14555,plain,(
    '#skF_8'('#skF_10',k2_relat_1('#skF_10'),'#skF_5'('#skF_10',k1_xboole_0)) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_14507,c_3905])).

tff(c_14567,plain,
    ( k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',k1_xboole_0)
    | ~ r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_14555,c_32])).

tff(c_14604,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_14507,c_14567])).

tff(c_3918,plain,(
    ! [D_56] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),k1_funct_1('#skF_10',D_56)) = '#skF_9'
      | ~ r2_hidden(D_56,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_30,c_3914])).

tff(c_4011,plain,(
    ! [D_5825] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),k1_funct_1('#skF_10',D_5825)) = '#skF_9'
      | ~ r2_hidden(D_5825,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3918])).

tff(c_4020,plain,(
    ! [D_5825] :
      ( k1_funct_1('#skF_10',D_5825) = k1_funct_1('#skF_10','#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_10',D_5825),k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_5825,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4011,c_32])).

tff(c_4044,plain,(
    ! [D_5825] :
      ( k1_funct_1('#skF_10',D_5825) = k1_funct_1('#skF_10','#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_10',D_5825),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_5825,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4020])).

tff(c_280191,plain,(
    ! [D_195134] :
      ( k1_funct_1('#skF_10',D_195134) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(k1_funct_1('#skF_10',D_195134),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_195134,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14604,c_4044])).

tff(c_280475,plain,(
    ! [D_56] :
      ( k1_funct_1('#skF_10',D_56) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(D_56,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_30,c_280191])).

tff(c_280497,plain,(
    ! [D_195685] :
      ( k1_funct_1('#skF_10',D_195685) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(D_195685,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_280475])).

tff(c_280765,plain,(
    ! [C_53] :
      ( k1_funct_1('#skF_10','#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_53)) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_53,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_34,c_280497])).

tff(c_285858,plain,(
    ! [C_198991] :
      ( k1_funct_1('#skF_10','#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_198991)) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_198991,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_280765])).

tff(c_285886,plain,(
    ! [C_198991] :
      ( C_198991 = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_198991,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_198991,k2_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285858,c_32])).

tff(c_286777,plain,(
    ! [C_199542] :
      ( C_199542 = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_199542,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_285886])).

tff(c_286981,plain,(
    ! [B_12] :
      ( '#skF_4'(k2_relat_1('#skF_10'),B_12) = '#skF_5'('#skF_10',k1_xboole_0)
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k2_relat_1('#skF_10') = k1_tarski(B_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_286777])).

tff(c_287034,plain,(
    ! [B_200093] :
      ( '#skF_4'(k2_relat_1('#skF_10'),B_200093) = '#skF_5'('#skF_10',k1_xboole_0)
      | k2_relat_1('#skF_10') = k1_tarski(B_200093) ) ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_286981])).

tff(c_287060,plain,(
    ! [B_200093] :
      ( B_200093 != '#skF_5'('#skF_10',k1_xboole_0)
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k2_relat_1('#skF_10') = k1_tarski(B_200093)
      | k2_relat_1('#skF_10') = k1_tarski(B_200093) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287034,c_20])).

tff(c_287884,plain,(
    k1_tarski('#skF_5'('#skF_10',k1_xboole_0)) = k2_relat_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_287060])).

tff(c_48,plain,(
    k1_tarski(k1_funct_1('#skF_10','#skF_9')) != k2_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14624,plain,(
    k1_tarski('#skF_5'('#skF_10',k1_xboole_0)) != k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14604,c_48])).

tff(c_287890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_287884,c_14624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:31:26 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.19/31.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.19/31.38  
% 43.19/31.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.19/31.38  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_5 > #skF_4
% 43.19/31.38  
% 43.19/31.38  %Foreground sorts:
% 43.19/31.38  
% 43.19/31.38  
% 43.19/31.38  %Background operators:
% 43.19/31.38  
% 43.19/31.38  
% 43.19/31.38  %Foreground operators:
% 43.19/31.38  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 43.19/31.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 43.19/31.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.19/31.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 43.19/31.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 43.19/31.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 43.19/31.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 43.19/31.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 43.19/31.38  tff('#skF_10', type, '#skF_10': $i).
% 43.19/31.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 43.19/31.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 43.19/31.38  tff('#skF_9', type, '#skF_9': $i).
% 43.19/31.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 43.19/31.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.19/31.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 43.19/31.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.19/31.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 43.19/31.38  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 43.19/31.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 43.19/31.38  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 43.19/31.38  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 43.19/31.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 43.19/31.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 43.19/31.38  
% 43.19/31.40  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 43.19/31.40  tff(f_63, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 43.19/31.40  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 43.19/31.40  tff(f_93, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 43.19/31.40  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 43.19/31.40  tff(f_69, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 43.19/31.40  tff(f_60, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 43.19/31.40  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 43.19/31.40  tff(c_166, plain, (![A_70, B_71]: (k2_xboole_0(k1_tarski(A_70), B_71)=B_71 | ~r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_46])).
% 43.19/31.40  tff(c_24, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 43.19/31.40  tff(c_180, plain, (![A_70]: (~r2_hidden(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_166, c_24])).
% 43.19/31.40  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 43.19/31.40  tff(c_50, plain, (k1_tarski('#skF_9')=k1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_93])).
% 43.19/31.40  tff(c_76, plain, (![C_62, A_63]: (C_62=A_63 | ~r2_hidden(C_62, k1_tarski(A_63)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 43.19/31.40  tff(c_91, plain, (![C_65]: (C_65='#skF_9' | ~r2_hidden(C_65, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_76])).
% 43.19/31.40  tff(c_99, plain, ('#skF_1'(k1_relat_1('#skF_10'))='#skF_9' | k1_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_91])).
% 43.19/31.40  tff(c_120, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_99])).
% 43.19/31.40  tff(c_59, plain, (![C_57]: (r2_hidden(C_57, k1_tarski(C_57)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 43.19/31.40  tff(c_62, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_59])).
% 43.19/31.40  tff(c_123, plain, (r2_hidden('#skF_9', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_62])).
% 43.19/31.40  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_123])).
% 43.19/31.40  tff(c_184, plain, (k1_relat_1('#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 43.19/31.40  tff(c_54, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_93])).
% 43.19/31.40  tff(c_201, plain, (![A_73]: (k1_relat_1(A_73)=k1_xboole_0 | k2_relat_1(A_73)!=k1_xboole_0 | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_69])).
% 43.19/31.40  tff(c_204, plain, (k1_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_201])).
% 43.19/31.40  tff(c_207, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_184, c_204])).
% 43.19/31.40  tff(c_22, plain, (![A_11, B_12]: (r2_hidden('#skF_4'(A_11, B_12), A_11) | k1_xboole_0=A_11 | k1_tarski(B_12)=A_11)), inference(cnfTransformation, [status(thm)], [f_60])).
% 43.19/31.40  tff(c_52, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_93])).
% 43.19/31.40  tff(c_34, plain, (![A_17, C_53]: (r2_hidden('#skF_8'(A_17, k2_relat_1(A_17), C_53), k1_relat_1(A_17)) | ~r2_hidden(C_53, k2_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_84])).
% 43.19/31.40  tff(c_30, plain, (![A_17, D_56]: (r2_hidden(k1_funct_1(A_17, D_56), k2_relat_1(A_17)) | ~r2_hidden(D_56, k1_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_84])).
% 43.19/31.40  tff(c_208, plain, (![A_74, B_75]: (k2_xboole_0(k1_tarski(A_74), B_75)=B_75 | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_46])).
% 43.19/31.40  tff(c_222, plain, (![A_74]: (~r2_hidden(A_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_24])).
% 43.19/31.40  tff(c_270, plain, (![A_83, B_84]: (r2_hidden('#skF_4'(A_83, B_84), A_83) | k1_xboole_0=A_83 | k1_tarski(B_84)=A_83)), inference(cnfTransformation, [status(thm)], [f_60])).
% 43.19/31.40  tff(c_82, plain, (![C_62]: (C_62='#skF_9' | ~r2_hidden(C_62, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_76])).
% 43.19/31.40  tff(c_277, plain, (![B_84]: ('#skF_4'(k1_relat_1('#skF_10'), B_84)='#skF_9' | k1_relat_1('#skF_10')=k1_xboole_0 | k1_tarski(B_84)=k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_270, c_82])).
% 43.19/31.40  tff(c_289, plain, (![B_85]: ('#skF_4'(k1_relat_1('#skF_10'), B_85)='#skF_9' | k1_tarski(B_85)=k1_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_184, c_277])).
% 43.19/31.40  tff(c_20, plain, (![A_11, B_12]: ('#skF_4'(A_11, B_12)!=B_12 | k1_xboole_0=A_11 | k1_tarski(B_12)=A_11)), inference(cnfTransformation, [status(thm)], [f_60])).
% 43.19/31.40  tff(c_297, plain, (![B_85]: (B_85!='#skF_9' | k1_relat_1('#skF_10')=k1_xboole_0 | k1_tarski(B_85)=k1_relat_1('#skF_10') | k1_tarski(B_85)=k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_289, c_20])).
% 43.19/31.40  tff(c_304, plain, (![B_85]: (B_85!='#skF_9' | k1_tarski(B_85)=k1_relat_1('#skF_10') | k1_tarski(B_85)=k1_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_184, c_297])).
% 43.19/31.40  tff(c_369, plain, (![B_89]: (B_89!='#skF_9' | k1_tarski(B_89)=k1_relat_1('#skF_10'))), inference(factorization, [status(thm), theory('equality')], [c_304])).
% 43.19/31.40  tff(c_6, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 43.19/31.40  tff(c_401, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_369, c_6])).
% 43.19/31.40  tff(c_4332, plain, (![A_6508, B_6509]: (r2_hidden('#skF_6'(A_6508, B_6509), k1_relat_1(A_6508)) | r2_hidden('#skF_7'(A_6508, B_6509), B_6509) | k2_relat_1(A_6508)=B_6509 | ~v1_funct_1(A_6508) | ~v1_relat_1(A_6508))), inference(cnfTransformation, [status(thm)], [f_84])).
% 43.19/31.40  tff(c_4347, plain, (![B_6509]: ('#skF_6'('#skF_10', B_6509)='#skF_9' | r2_hidden('#skF_7'('#skF_10', B_6509), B_6509) | k2_relat_1('#skF_10')=B_6509 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_4332, c_82])).
% 43.19/31.40  tff(c_4450, plain, (![B_6585]: ('#skF_6'('#skF_10', B_6585)='#skF_9' | r2_hidden('#skF_7'('#skF_10', B_6585), B_6585) | k2_relat_1('#skF_10')=B_6585)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4347])).
% 43.19/31.40  tff(c_213, plain, (![B_75, A_74]: (k1_xboole_0!=B_75 | ~r2_hidden(A_74, B_75))), inference(superposition, [status(thm), theory('equality')], [c_208, c_24])).
% 43.19/31.40  tff(c_4671, plain, ('#skF_6'('#skF_10', k1_xboole_0)='#skF_9' | k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_4450, c_213])).
% 43.19/31.40  tff(c_3833, plain, (![A_5445, C_5446]: (r2_hidden('#skF_8'(A_5445, k2_relat_1(A_5445), C_5446), k1_relat_1(A_5445)) | ~r2_hidden(C_5446, k2_relat_1(A_5445)) | ~v1_funct_1(A_5445) | ~v1_relat_1(A_5445))), inference(cnfTransformation, [status(thm)], [f_84])).
% 43.19/31.40  tff(c_3848, plain, (![C_5446]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_5446)='#skF_9' | ~r2_hidden(C_5446, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_3833, c_82])).
% 43.19/31.40  tff(c_3914, plain, (![C_5522]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_5522)='#skF_9' | ~r2_hidden(C_5522, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3848])).
% 43.19/31.40  tff(c_3936, plain, ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), '#skF_1'(k2_relat_1('#skF_10')))='#skF_9' | k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_3914])).
% 43.19/31.40  tff(c_3947, plain, ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), '#skF_1'(k2_relat_1('#skF_10')))='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_207, c_3936])).
% 43.19/31.40  tff(c_32, plain, (![A_17, C_53]: (k1_funct_1(A_17, '#skF_8'(A_17, k2_relat_1(A_17), C_53))=C_53 | ~r2_hidden(C_53, k2_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_84])).
% 43.19/31.40  tff(c_3954, plain, ('#skF_1'(k2_relat_1('#skF_10'))=k1_funct_1('#skF_10', '#skF_9') | ~r2_hidden('#skF_1'(k2_relat_1('#skF_10')), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3947, c_32])).
% 43.19/31.40  tff(c_3974, plain, ('#skF_1'(k2_relat_1('#skF_10'))=k1_funct_1('#skF_10', '#skF_9') | ~r2_hidden('#skF_1'(k2_relat_1('#skF_10')), k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3954])).
% 43.19/31.40  tff(c_4048, plain, (~r2_hidden('#skF_1'(k2_relat_1('#skF_10')), k2_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_3974])).
% 43.19/31.40  tff(c_4060, plain, (k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_4048])).
% 43.19/31.40  tff(c_4064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_4060])).
% 43.19/31.40  tff(c_4065, plain, ('#skF_1'(k2_relat_1('#skF_10'))=k1_funct_1('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_3974])).
% 43.19/31.40  tff(c_4066, plain, (r2_hidden('#skF_1'(k2_relat_1('#skF_10')), k2_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_3974])).
% 43.19/31.40  tff(c_4139, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_9'), k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_4065, c_4066])).
% 43.19/31.40  tff(c_4672, plain, (r2_hidden(k1_funct_1('#skF_10', '#skF_9'), k1_xboole_0) | '#skF_6'('#skF_10', k1_xboole_0)='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_4671, c_4139])).
% 43.19/31.40  tff(c_5003, plain, ('#skF_6'('#skF_10', k1_xboole_0)='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_222, c_4672])).
% 43.19/31.40  tff(c_5142, plain, (![A_9266, B_9267]: (k1_funct_1(A_9266, '#skF_6'(A_9266, B_9267))='#skF_5'(A_9266, B_9267) | r2_hidden('#skF_7'(A_9266, B_9267), B_9267) | k2_relat_1(A_9266)=B_9267 | ~v1_funct_1(A_9266) | ~v1_relat_1(A_9266))), inference(cnfTransformation, [status(thm)], [f_84])).
% 43.19/31.40  tff(c_14418, plain, (![A_22303, B_22304]: (r2_hidden('#skF_5'(A_22303, B_22304), k2_relat_1(A_22303)) | ~r2_hidden('#skF_6'(A_22303, B_22304), k1_relat_1(A_22303)) | ~v1_funct_1(A_22303) | ~v1_relat_1(A_22303) | r2_hidden('#skF_7'(A_22303, B_22304), B_22304) | k2_relat_1(A_22303)=B_22304 | ~v1_funct_1(A_22303) | ~v1_relat_1(A_22303))), inference(superposition, [status(thm), theory('equality')], [c_5142, c_30])).
% 43.19/31.40  tff(c_14442, plain, (r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10')) | ~r2_hidden('#skF_9', k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | r2_hidden('#skF_7'('#skF_10', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_5003, c_14418])).
% 43.19/31.40  tff(c_14506, plain, (r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10')) | r2_hidden('#skF_7'('#skF_10', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_54, c_52, c_401, c_14442])).
% 43.19/31.40  tff(c_14507, plain, (r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_207, c_222, c_14506])).
% 43.19/31.40  tff(c_3905, plain, (![C_5446]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_5446)='#skF_9' | ~r2_hidden(C_5446, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3848])).
% 43.19/31.40  tff(c_14555, plain, ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), '#skF_5'('#skF_10', k1_xboole_0))='#skF_9'), inference(resolution, [status(thm)], [c_14507, c_3905])).
% 43.19/31.40  tff(c_14567, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_14555, c_32])).
% 43.19/31.40  tff(c_14604, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_14507, c_14567])).
% 43.19/31.40  tff(c_3918, plain, (![D_56]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), k1_funct_1('#skF_10', D_56))='#skF_9' | ~r2_hidden(D_56, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_30, c_3914])).
% 43.19/31.40  tff(c_4011, plain, (![D_5825]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), k1_funct_1('#skF_10', D_5825))='#skF_9' | ~r2_hidden(D_5825, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3918])).
% 43.19/31.40  tff(c_4020, plain, (![D_5825]: (k1_funct_1('#skF_10', D_5825)=k1_funct_1('#skF_10', '#skF_9') | ~r2_hidden(k1_funct_1('#skF_10', D_5825), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_5825, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_4011, c_32])).
% 43.19/31.40  tff(c_4044, plain, (![D_5825]: (k1_funct_1('#skF_10', D_5825)=k1_funct_1('#skF_10', '#skF_9') | ~r2_hidden(k1_funct_1('#skF_10', D_5825), k2_relat_1('#skF_10')) | ~r2_hidden(D_5825, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4020])).
% 43.19/31.40  tff(c_280191, plain, (![D_195134]: (k1_funct_1('#skF_10', D_195134)='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(k1_funct_1('#skF_10', D_195134), k2_relat_1('#skF_10')) | ~r2_hidden(D_195134, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_14604, c_4044])).
% 43.19/31.40  tff(c_280475, plain, (![D_56]: (k1_funct_1('#skF_10', D_56)='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(D_56, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_30, c_280191])).
% 43.19/31.40  tff(c_280497, plain, (![D_195685]: (k1_funct_1('#skF_10', D_195685)='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(D_195685, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_280475])).
% 43.19/31.40  tff(c_280765, plain, (![C_53]: (k1_funct_1('#skF_10', '#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_53))='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_53, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_34, c_280497])).
% 43.19/31.40  tff(c_285858, plain, (![C_198991]: (k1_funct_1('#skF_10', '#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_198991))='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_198991, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_280765])).
% 43.19/31.40  tff(c_285886, plain, (![C_198991]: (C_198991='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_198991, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_198991, k2_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_285858, c_32])).
% 43.19/31.40  tff(c_286777, plain, (![C_199542]: (C_199542='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_199542, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_285886])).
% 43.19/31.40  tff(c_286981, plain, (![B_12]: ('#skF_4'(k2_relat_1('#skF_10'), B_12)='#skF_5'('#skF_10', k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')=k1_tarski(B_12))), inference(resolution, [status(thm)], [c_22, c_286777])).
% 43.19/31.40  tff(c_287034, plain, (![B_200093]: ('#skF_4'(k2_relat_1('#skF_10'), B_200093)='#skF_5'('#skF_10', k1_xboole_0) | k2_relat_1('#skF_10')=k1_tarski(B_200093))), inference(negUnitSimplification, [status(thm)], [c_207, c_286981])).
% 43.19/31.40  tff(c_287060, plain, (![B_200093]: (B_200093!='#skF_5'('#skF_10', k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')=k1_tarski(B_200093) | k2_relat_1('#skF_10')=k1_tarski(B_200093))), inference(superposition, [status(thm), theory('equality')], [c_287034, c_20])).
% 43.19/31.40  tff(c_287884, plain, (k1_tarski('#skF_5'('#skF_10', k1_xboole_0))=k2_relat_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_207, c_287060])).
% 43.19/31.40  tff(c_48, plain, (k1_tarski(k1_funct_1('#skF_10', '#skF_9'))!=k2_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_93])).
% 43.19/31.40  tff(c_14624, plain, (k1_tarski('#skF_5'('#skF_10', k1_xboole_0))!=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_14604, c_48])).
% 43.19/31.40  tff(c_287890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_287884, c_14624])).
% 43.19/31.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.19/31.40  
% 43.19/31.40  Inference rules
% 43.19/31.40  ----------------------
% 43.19/31.40  #Ref     : 30
% 43.19/31.40  #Sup     : 37369
% 43.19/31.40  #Fact    : 8
% 43.19/31.40  #Define  : 0
% 43.19/31.40  #Split   : 34
% 43.19/31.40  #Chain   : 0
% 43.19/31.40  #Close   : 0
% 43.19/31.40  
% 43.19/31.40  Ordering : KBO
% 43.19/31.40  
% 43.19/31.40  Simplification rules
% 43.19/31.40  ----------------------
% 43.19/31.40  #Subsume      : 9656
% 43.19/31.40  #Demod        : 3886
% 43.19/31.40  #Tautology    : 3511
% 43.19/31.40  #SimpNegUnit  : 724
% 43.19/31.40  #BackRed      : 106
% 43.19/31.40  
% 43.19/31.40  #Partial instantiations: 131153
% 43.19/31.40  #Strategies tried      : 1
% 43.19/31.40  
% 43.19/31.40  Timing (in seconds)
% 43.19/31.40  ----------------------
% 43.19/31.40  Preprocessing        : 0.32
% 43.19/31.40  Parsing              : 0.16
% 43.19/31.40  CNF conversion       : 0.03
% 43.19/31.40  Main loop            : 30.32
% 43.19/31.40  Inferencing          : 4.01
% 43.19/31.40  Reduction            : 5.40
% 43.19/31.40  Demodulation         : 3.51
% 43.19/31.40  BG Simplification    : 0.59
% 43.19/31.40  Subsumption          : 19.14
% 43.19/31.40  Abstraction          : 0.62
% 43.19/31.40  MUC search           : 0.00
% 43.19/31.40  Cooper               : 0.00
% 43.19/31.40  Total                : 30.68
% 43.19/31.40  Index Insertion      : 0.00
% 43.19/31.40  Index Deletion       : 0.00
% 43.19/31.40  Index Matching       : 0.00
% 43.19/31.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
