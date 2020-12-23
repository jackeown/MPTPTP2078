%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:14 EST 2020

% Result     : Theorem 8.66s
% Output     : CNFRefutation 8.97s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 549 expanded)
%              Number of leaves         :   25 ( 199 expanded)
%              Depth                    :   14
%              Number of atoms          :  217 (1489 expanded)
%              Number of equality atoms :   80 ( 692 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_35,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_58,axiom,(
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

tff(c_15836,plain,(
    ! [A_4749,B_4750] :
      ( r2_hidden('#skF_1'(A_4749,B_4750),A_4749)
      | r1_tarski(A_4749,B_4750) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_15841,plain,(
    ! [A_4749] : r1_tarski(A_4749,A_4749) ),
    inference(resolution,[status(thm)],[c_15836,c_4])).

tff(c_36,plain,(
    ! [A_47,B_48] : k1_relat_1('#skF_6'(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    ! [A_47,B_48] : v1_relat_1('#skF_6'(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_65,plain,(
    ! [A_62] :
      ( k1_relat_1(A_62) != k1_xboole_0
      | k1_xboole_0 = A_62
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [A_47,B_48] :
      ( k1_relat_1('#skF_6'(A_47,B_48)) != k1_xboole_0
      | '#skF_6'(A_47,B_48) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_72,plain,(
    ! [A_63,B_64] :
      ( k1_xboole_0 != A_63
      | '#skF_6'(A_63,B_64) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_68])).

tff(c_80,plain,(
    ! [A_63] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_63 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_40])).

tff(c_94,plain,(
    ! [A_63] : k1_xboole_0 != A_63 ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_8,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_8])).

tff(c_100,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_38,plain,(
    ! [A_47,B_48] : v1_funct_1('#skF_6'(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_82,plain,(
    ! [A_63] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_63 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_38])).

tff(c_108,plain,(
    ! [A_63] : k1_xboole_0 != A_63 ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_8])).

tff(c_114,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_71,plain,(
    ! [B_48] : '#skF_6'(k1_xboole_0,B_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_68])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    ! [A_80,D_81] :
      ( r2_hidden(k1_funct_1(A_80,D_81),k2_relat_1(A_80))
      | ~ r2_hidden(D_81,k1_relat_1(A_80))
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_168,plain,(
    ! [D_81] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_81),k1_xboole_0)
      | ~ r2_hidden(D_81,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_160])).

tff(c_173,plain,(
    ! [D_81] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_81),k1_xboole_0)
      | ~ r2_hidden(D_81,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_114,c_10,c_168])).

tff(c_34,plain,(
    ! [A_47,B_48,D_53] :
      ( k1_funct_1('#skF_6'(A_47,B_48),D_53) = B_48
      | ~ r2_hidden(D_53,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_165,plain,(
    ! [B_48,A_47,D_53] :
      ( r2_hidden(B_48,k2_relat_1('#skF_6'(A_47,B_48)))
      | ~ r2_hidden(D_53,k1_relat_1('#skF_6'(A_47,B_48)))
      | ~ v1_funct_1('#skF_6'(A_47,B_48))
      | ~ v1_relat_1('#skF_6'(A_47,B_48))
      | ~ r2_hidden(D_53,A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_160])).

tff(c_178,plain,(
    ! [B_83,A_84,D_85] :
      ( r2_hidden(B_83,k2_relat_1('#skF_6'(A_84,B_83)))
      | ~ r2_hidden(D_85,A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_165])).

tff(c_180,plain,(
    ! [B_83,D_81] :
      ( r2_hidden(B_83,k2_relat_1('#skF_6'(k1_xboole_0,B_83)))
      | ~ r2_hidden(D_81,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_173,c_178])).

tff(c_186,plain,(
    ! [B_83,D_81] :
      ( r2_hidden(B_83,k1_xboole_0)
      | ~ r2_hidden(D_81,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_71,c_180])).

tff(c_189,plain,(
    ! [D_81] : ~ r2_hidden(D_81,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_391,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_3'(A_122,B_123),k1_relat_1(A_122))
      | r2_hidden('#skF_4'(A_122,B_123),B_123)
      | k2_relat_1(A_122) = B_123
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_411,plain,(
    ! [B_123] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_123),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_123),B_123)
      | k2_relat_1(k1_xboole_0) = B_123
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_391])).

tff(c_421,plain,(
    ! [B_123] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_123),k1_xboole_0)
      | r2_hidden('#skF_4'(k1_xboole_0,B_123),B_123)
      | k1_xboole_0 = B_123 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_114,c_8,c_411])).

tff(c_422,plain,(
    ! [B_123] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_123),B_123)
      | k1_xboole_0 = B_123 ) ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_421])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden('#skF_1'(A_69,B_70),B_70)
      | r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_133,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_264,plain,(
    ! [A_98,C_99] :
      ( r2_hidden('#skF_5'(A_98,k2_relat_1(A_98),C_99),k1_relat_1(A_98))
      | ~ r2_hidden(C_99,k2_relat_1(A_98))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_282,plain,(
    ! [A_98,C_99,B_2] :
      ( r2_hidden('#skF_5'(A_98,k2_relat_1(A_98),C_99),B_2)
      | ~ r1_tarski(k1_relat_1(A_98),B_2)
      | ~ r2_hidden(C_99,k2_relat_1(A_98))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_264,c_2])).

tff(c_190,plain,(
    ! [A_86,C_87] :
      ( k1_funct_1(A_86,'#skF_5'(A_86,k2_relat_1(A_86),C_87)) = C_87
      | ~ r2_hidden(C_87,k2_relat_1(A_86))
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_204,plain,(
    ! [C_87,B_48,A_47] :
      ( C_87 = B_48
      | ~ r2_hidden('#skF_5'('#skF_6'(A_47,B_48),k2_relat_1('#skF_6'(A_47,B_48)),C_87),A_47)
      | ~ r2_hidden(C_87,k2_relat_1('#skF_6'(A_47,B_48)))
      | ~ v1_funct_1('#skF_6'(A_47,B_48))
      | ~ v1_relat_1('#skF_6'(A_47,B_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_34])).

tff(c_2379,plain,(
    ! [C_271,B_272,A_273] :
      ( C_271 = B_272
      | ~ r2_hidden('#skF_5'('#skF_6'(A_273,B_272),k2_relat_1('#skF_6'(A_273,B_272)),C_271),A_273)
      | ~ r2_hidden(C_271,k2_relat_1('#skF_6'(A_273,B_272))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_204])).

tff(c_2383,plain,(
    ! [C_99,B_272,B_2] :
      ( C_99 = B_272
      | ~ r1_tarski(k1_relat_1('#skF_6'(B_2,B_272)),B_2)
      | ~ r2_hidden(C_99,k2_relat_1('#skF_6'(B_2,B_272)))
      | ~ v1_funct_1('#skF_6'(B_2,B_272))
      | ~ v1_relat_1('#skF_6'(B_2,B_272)) ) ),
    inference(resolution,[status(thm)],[c_282,c_2379])).

tff(c_2427,plain,(
    ! [C_276,B_277,B_278] :
      ( C_276 = B_277
      | ~ r2_hidden(C_276,k2_relat_1('#skF_6'(B_278,B_277))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_133,c_36,c_2383])).

tff(c_13110,plain,(
    ! [B_2977,B_2978,B_2979] :
      ( '#skF_1'(k2_relat_1('#skF_6'(B_2977,B_2978)),B_2979) = B_2978
      | r1_tarski(k2_relat_1('#skF_6'(B_2977,B_2978)),B_2979) ) ),
    inference(resolution,[status(thm)],[c_6,c_2427])).

tff(c_42,plain,(
    ! [C_55] :
      ( ~ r1_tarski(k2_relat_1(C_55),'#skF_7')
      | k1_relat_1(C_55) != '#skF_8'
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13224,plain,(
    ! [B_2977,B_2978] :
      ( k1_relat_1('#skF_6'(B_2977,B_2978)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(B_2977,B_2978))
      | ~ v1_relat_1('#skF_6'(B_2977,B_2978))
      | '#skF_1'(k2_relat_1('#skF_6'(B_2977,B_2978)),'#skF_7') = B_2978 ) ),
    inference(resolution,[status(thm)],[c_13110,c_42])).

tff(c_13364,plain,(
    ! [B_2997,B_2998] :
      ( B_2997 != '#skF_8'
      | '#skF_1'(k2_relat_1('#skF_6'(B_2997,B_2998)),'#skF_7') = B_2998 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_13224])).

tff(c_14000,plain,(
    ! [B_3114,B_3115] :
      ( ~ r2_hidden(B_3114,'#skF_7')
      | r1_tarski(k2_relat_1('#skF_6'(B_3115,B_3114)),'#skF_7')
      | B_3115 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13364,c_4])).

tff(c_14034,plain,(
    ! [B_3115,B_3114] :
      ( k1_relat_1('#skF_6'(B_3115,B_3114)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(B_3115,B_3114))
      | ~ v1_relat_1('#skF_6'(B_3115,B_3114))
      | ~ r2_hidden(B_3114,'#skF_7')
      | B_3115 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_14000,c_42])).

tff(c_14120,plain,(
    ! [B_3114,B_3115] :
      ( ~ r2_hidden(B_3114,'#skF_7')
      | B_3115 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_14034])).

tff(c_14135,plain,(
    ! [B_3115] : B_3115 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_14120])).

tff(c_14139,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_14135])).

tff(c_14142,plain,(
    ! [B_3133] : ~ r2_hidden(B_3133,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_14120])).

tff(c_14184,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_422,c_14142])).

tff(c_14206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_14184])).

tff(c_14207,plain,(
    ! [B_83] : r2_hidden(B_83,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_18,plain,(
    ! [A_7,C_43] :
      ( k1_funct_1(A_7,'#skF_5'(A_7,k2_relat_1(A_7),C_43)) = C_43
      | ~ r2_hidden(C_43,k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_70,plain,(
    ! [A_47,B_48] :
      ( k1_xboole_0 != A_47
      | '#skF_6'(A_47,B_48) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_68])).

tff(c_142,plain,(
    ! [A_75,B_76,D_77] :
      ( k1_funct_1('#skF_6'(A_75,B_76),D_77) = B_76
      | ~ r2_hidden(D_77,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14290,plain,(
    ! [D_3160,B_3161,A_3162] :
      ( k1_funct_1(k1_xboole_0,D_3160) = B_3161
      | ~ r2_hidden(D_3160,A_3162)
      | k1_xboole_0 != A_3162 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_142])).

tff(c_14303,plain,(
    ! [B_3163,B_3164] : k1_funct_1(k1_xboole_0,B_3163) = B_3164 ),
    inference(resolution,[status(thm)],[c_14207,c_14290])).

tff(c_14585,plain,(
    ! [C_43,B_3164] :
      ( C_43 = B_3164
      | ~ r2_hidden(C_43,k2_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_14303])).

tff(c_14716,plain,(
    ! [C_4050,B_4051] : C_4050 = B_4051 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_114,c_14207,c_8,c_14585])).

tff(c_15412,plain,(
    ! [B_4051] : B_4051 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_14716,c_53])).

tff(c_15724,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15412])).

tff(c_15725,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_14,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_15771,plain,(
    ! [A_4742] :
      ( k1_relat_1(A_4742) != '#skF_8'
      | A_4742 = '#skF_8'
      | ~ v1_relat_1(A_4742) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15725,c_15725,c_14])).

tff(c_15774,plain,(
    ! [A_47,B_48] :
      ( k1_relat_1('#skF_6'(A_47,B_48)) != '#skF_8'
      | '#skF_6'(A_47,B_48) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_40,c_15771])).

tff(c_15778,plain,(
    ! [A_4743,B_4744] :
      ( A_4743 != '#skF_8'
      | '#skF_6'(A_4743,B_4744) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_15774])).

tff(c_15788,plain,(
    ! [A_4743] :
      ( v1_relat_1('#skF_8')
      | A_4743 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15778,c_40])).

tff(c_15806,plain,(
    ! [A_4743] : A_4743 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_15788])).

tff(c_15728,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15725,c_15725,c_10])).

tff(c_15817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15806,c_15728])).

tff(c_15818,plain,(
    v1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_15788])).

tff(c_15786,plain,(
    ! [A_4743] :
      ( v1_funct_1('#skF_8')
      | A_4743 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15778,c_38])).

tff(c_15795,plain,(
    ! [A_4743] : A_4743 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_15786])).

tff(c_15804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15795,c_15728])).

tff(c_15805,plain,(
    v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_15786])).

tff(c_15727,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15725,c_15725,c_8])).

tff(c_15726,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_15733,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15725,c_15726])).

tff(c_15749,plain,(
    ! [C_4738] :
      ( ~ r1_tarski(k2_relat_1(C_4738),'#skF_8')
      | k1_relat_1(C_4738) != '#skF_8'
      | ~ v1_funct_1(C_4738)
      | ~ v1_relat_1(C_4738) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15733,c_42])).

tff(c_15752,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_15727,c_15749])).

tff(c_15754,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15728,c_15752])).

tff(c_15834,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15818,c_15805,c_15754])).

tff(c_15856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15841,c_15834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.66/2.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.97/3.00  
% 8.97/3.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.97/3.01  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 8.97/3.01  
% 8.97/3.01  %Foreground sorts:
% 8.97/3.01  
% 8.97/3.01  
% 8.97/3.01  %Background operators:
% 8.97/3.01  
% 8.97/3.01  
% 8.97/3.01  %Foreground operators:
% 8.97/3.01  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.97/3.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.97/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.97/3.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.97/3.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.97/3.01  tff('#skF_7', type, '#skF_7': $i).
% 8.97/3.01  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.97/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.97/3.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.97/3.01  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.97/3.01  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.97/3.01  tff('#skF_8', type, '#skF_8': $i).
% 8.97/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.97/3.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.97/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.97/3.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.97/3.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.97/3.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.97/3.01  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.97/3.01  
% 8.97/3.03  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.97/3.03  tff(f_70, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 8.97/3.03  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 8.97/3.03  tff(f_35, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.97/3.03  tff(f_88, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 8.97/3.03  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 8.97/3.03  tff(c_15836, plain, (![A_4749, B_4750]: (r2_hidden('#skF_1'(A_4749, B_4750), A_4749) | r1_tarski(A_4749, B_4750))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.97/3.03  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.97/3.03  tff(c_15841, plain, (![A_4749]: (r1_tarski(A_4749, A_4749))), inference(resolution, [status(thm)], [c_15836, c_4])).
% 8.97/3.03  tff(c_36, plain, (![A_47, B_48]: (k1_relat_1('#skF_6'(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.97/3.03  tff(c_40, plain, (![A_47, B_48]: (v1_relat_1('#skF_6'(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.97/3.03  tff(c_65, plain, (![A_62]: (k1_relat_1(A_62)!=k1_xboole_0 | k1_xboole_0=A_62 | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.97/3.03  tff(c_68, plain, (![A_47, B_48]: (k1_relat_1('#skF_6'(A_47, B_48))!=k1_xboole_0 | '#skF_6'(A_47, B_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_65])).
% 8.97/3.03  tff(c_72, plain, (![A_63, B_64]: (k1_xboole_0!=A_63 | '#skF_6'(A_63, B_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_68])).
% 8.97/3.03  tff(c_80, plain, (![A_63]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_63)), inference(superposition, [status(thm), theory('equality')], [c_72, c_40])).
% 8.97/3.03  tff(c_94, plain, (![A_63]: (k1_xboole_0!=A_63)), inference(splitLeft, [status(thm)], [c_80])).
% 8.97/3.03  tff(c_8, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.97/3.03  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_8])).
% 8.97/3.03  tff(c_100, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_80])).
% 8.97/3.03  tff(c_38, plain, (![A_47, B_48]: (v1_funct_1('#skF_6'(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.97/3.03  tff(c_82, plain, (![A_63]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_63)), inference(superposition, [status(thm), theory('equality')], [c_72, c_38])).
% 8.97/3.03  tff(c_108, plain, (![A_63]: (k1_xboole_0!=A_63)), inference(splitLeft, [status(thm)], [c_82])).
% 8.97/3.03  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_8])).
% 8.97/3.03  tff(c_114, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_82])).
% 8.97/3.03  tff(c_44, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.97/3.03  tff(c_53, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_44])).
% 8.97/3.03  tff(c_71, plain, (![B_48]: ('#skF_6'(k1_xboole_0, B_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_68])).
% 8.97/3.03  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.97/3.03  tff(c_160, plain, (![A_80, D_81]: (r2_hidden(k1_funct_1(A_80, D_81), k2_relat_1(A_80)) | ~r2_hidden(D_81, k1_relat_1(A_80)) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.97/3.03  tff(c_168, plain, (![D_81]: (r2_hidden(k1_funct_1(k1_xboole_0, D_81), k1_xboole_0) | ~r2_hidden(D_81, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_160])).
% 8.97/3.03  tff(c_173, plain, (![D_81]: (r2_hidden(k1_funct_1(k1_xboole_0, D_81), k1_xboole_0) | ~r2_hidden(D_81, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_114, c_10, c_168])).
% 8.97/3.03  tff(c_34, plain, (![A_47, B_48, D_53]: (k1_funct_1('#skF_6'(A_47, B_48), D_53)=B_48 | ~r2_hidden(D_53, A_47))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.97/3.03  tff(c_165, plain, (![B_48, A_47, D_53]: (r2_hidden(B_48, k2_relat_1('#skF_6'(A_47, B_48))) | ~r2_hidden(D_53, k1_relat_1('#skF_6'(A_47, B_48))) | ~v1_funct_1('#skF_6'(A_47, B_48)) | ~v1_relat_1('#skF_6'(A_47, B_48)) | ~r2_hidden(D_53, A_47))), inference(superposition, [status(thm), theory('equality')], [c_34, c_160])).
% 8.97/3.03  tff(c_178, plain, (![B_83, A_84, D_85]: (r2_hidden(B_83, k2_relat_1('#skF_6'(A_84, B_83))) | ~r2_hidden(D_85, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_165])).
% 8.97/3.03  tff(c_180, plain, (![B_83, D_81]: (r2_hidden(B_83, k2_relat_1('#skF_6'(k1_xboole_0, B_83))) | ~r2_hidden(D_81, k1_xboole_0))), inference(resolution, [status(thm)], [c_173, c_178])).
% 8.97/3.03  tff(c_186, plain, (![B_83, D_81]: (r2_hidden(B_83, k1_xboole_0) | ~r2_hidden(D_81, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_71, c_180])).
% 8.97/3.03  tff(c_189, plain, (![D_81]: (~r2_hidden(D_81, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_186])).
% 8.97/3.03  tff(c_391, plain, (![A_122, B_123]: (r2_hidden('#skF_3'(A_122, B_123), k1_relat_1(A_122)) | r2_hidden('#skF_4'(A_122, B_123), B_123) | k2_relat_1(A_122)=B_123 | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.97/3.03  tff(c_411, plain, (![B_123]: (r2_hidden('#skF_3'(k1_xboole_0, B_123), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_123), B_123) | k2_relat_1(k1_xboole_0)=B_123 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_391])).
% 8.97/3.03  tff(c_421, plain, (![B_123]: (r2_hidden('#skF_3'(k1_xboole_0, B_123), k1_xboole_0) | r2_hidden('#skF_4'(k1_xboole_0, B_123), B_123) | k1_xboole_0=B_123)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_114, c_8, c_411])).
% 8.97/3.03  tff(c_422, plain, (![B_123]: (r2_hidden('#skF_4'(k1_xboole_0, B_123), B_123) | k1_xboole_0=B_123)), inference(negUnitSimplification, [status(thm)], [c_189, c_421])).
% 8.97/3.03  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.97/3.03  tff(c_128, plain, (![A_69, B_70]: (~r2_hidden('#skF_1'(A_69, B_70), B_70) | r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.97/3.03  tff(c_133, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_128])).
% 8.97/3.03  tff(c_264, plain, (![A_98, C_99]: (r2_hidden('#skF_5'(A_98, k2_relat_1(A_98), C_99), k1_relat_1(A_98)) | ~r2_hidden(C_99, k2_relat_1(A_98)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.97/3.03  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.97/3.03  tff(c_282, plain, (![A_98, C_99, B_2]: (r2_hidden('#skF_5'(A_98, k2_relat_1(A_98), C_99), B_2) | ~r1_tarski(k1_relat_1(A_98), B_2) | ~r2_hidden(C_99, k2_relat_1(A_98)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_264, c_2])).
% 8.97/3.03  tff(c_190, plain, (![A_86, C_87]: (k1_funct_1(A_86, '#skF_5'(A_86, k2_relat_1(A_86), C_87))=C_87 | ~r2_hidden(C_87, k2_relat_1(A_86)) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.97/3.03  tff(c_204, plain, (![C_87, B_48, A_47]: (C_87=B_48 | ~r2_hidden('#skF_5'('#skF_6'(A_47, B_48), k2_relat_1('#skF_6'(A_47, B_48)), C_87), A_47) | ~r2_hidden(C_87, k2_relat_1('#skF_6'(A_47, B_48))) | ~v1_funct_1('#skF_6'(A_47, B_48)) | ~v1_relat_1('#skF_6'(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_190, c_34])).
% 8.97/3.03  tff(c_2379, plain, (![C_271, B_272, A_273]: (C_271=B_272 | ~r2_hidden('#skF_5'('#skF_6'(A_273, B_272), k2_relat_1('#skF_6'(A_273, B_272)), C_271), A_273) | ~r2_hidden(C_271, k2_relat_1('#skF_6'(A_273, B_272))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_204])).
% 8.97/3.03  tff(c_2383, plain, (![C_99, B_272, B_2]: (C_99=B_272 | ~r1_tarski(k1_relat_1('#skF_6'(B_2, B_272)), B_2) | ~r2_hidden(C_99, k2_relat_1('#skF_6'(B_2, B_272))) | ~v1_funct_1('#skF_6'(B_2, B_272)) | ~v1_relat_1('#skF_6'(B_2, B_272)))), inference(resolution, [status(thm)], [c_282, c_2379])).
% 8.97/3.03  tff(c_2427, plain, (![C_276, B_277, B_278]: (C_276=B_277 | ~r2_hidden(C_276, k2_relat_1('#skF_6'(B_278, B_277))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_133, c_36, c_2383])).
% 8.97/3.03  tff(c_13110, plain, (![B_2977, B_2978, B_2979]: ('#skF_1'(k2_relat_1('#skF_6'(B_2977, B_2978)), B_2979)=B_2978 | r1_tarski(k2_relat_1('#skF_6'(B_2977, B_2978)), B_2979))), inference(resolution, [status(thm)], [c_6, c_2427])).
% 8.97/3.03  tff(c_42, plain, (![C_55]: (~r1_tarski(k2_relat_1(C_55), '#skF_7') | k1_relat_1(C_55)!='#skF_8' | ~v1_funct_1(C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.97/3.03  tff(c_13224, plain, (![B_2977, B_2978]: (k1_relat_1('#skF_6'(B_2977, B_2978))!='#skF_8' | ~v1_funct_1('#skF_6'(B_2977, B_2978)) | ~v1_relat_1('#skF_6'(B_2977, B_2978)) | '#skF_1'(k2_relat_1('#skF_6'(B_2977, B_2978)), '#skF_7')=B_2978)), inference(resolution, [status(thm)], [c_13110, c_42])).
% 8.97/3.03  tff(c_13364, plain, (![B_2997, B_2998]: (B_2997!='#skF_8' | '#skF_1'(k2_relat_1('#skF_6'(B_2997, B_2998)), '#skF_7')=B_2998)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_13224])).
% 8.97/3.03  tff(c_14000, plain, (![B_3114, B_3115]: (~r2_hidden(B_3114, '#skF_7') | r1_tarski(k2_relat_1('#skF_6'(B_3115, B_3114)), '#skF_7') | B_3115!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_13364, c_4])).
% 8.97/3.03  tff(c_14034, plain, (![B_3115, B_3114]: (k1_relat_1('#skF_6'(B_3115, B_3114))!='#skF_8' | ~v1_funct_1('#skF_6'(B_3115, B_3114)) | ~v1_relat_1('#skF_6'(B_3115, B_3114)) | ~r2_hidden(B_3114, '#skF_7') | B_3115!='#skF_8')), inference(resolution, [status(thm)], [c_14000, c_42])).
% 8.97/3.03  tff(c_14120, plain, (![B_3114, B_3115]: (~r2_hidden(B_3114, '#skF_7') | B_3115!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_14034])).
% 8.97/3.03  tff(c_14135, plain, (![B_3115]: (B_3115!='#skF_8')), inference(splitLeft, [status(thm)], [c_14120])).
% 8.97/3.03  tff(c_14139, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_14135])).
% 8.97/3.03  tff(c_14142, plain, (![B_3133]: (~r2_hidden(B_3133, '#skF_7'))), inference(splitRight, [status(thm)], [c_14120])).
% 8.97/3.03  tff(c_14184, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_422, c_14142])).
% 8.97/3.03  tff(c_14206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_14184])).
% 8.97/3.03  tff(c_14207, plain, (![B_83]: (r2_hidden(B_83, k1_xboole_0))), inference(splitRight, [status(thm)], [c_186])).
% 8.97/3.03  tff(c_18, plain, (![A_7, C_43]: (k1_funct_1(A_7, '#skF_5'(A_7, k2_relat_1(A_7), C_43))=C_43 | ~r2_hidden(C_43, k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.97/3.03  tff(c_70, plain, (![A_47, B_48]: (k1_xboole_0!=A_47 | '#skF_6'(A_47, B_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_68])).
% 8.97/3.03  tff(c_142, plain, (![A_75, B_76, D_77]: (k1_funct_1('#skF_6'(A_75, B_76), D_77)=B_76 | ~r2_hidden(D_77, A_75))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.97/3.03  tff(c_14290, plain, (![D_3160, B_3161, A_3162]: (k1_funct_1(k1_xboole_0, D_3160)=B_3161 | ~r2_hidden(D_3160, A_3162) | k1_xboole_0!=A_3162)), inference(superposition, [status(thm), theory('equality')], [c_70, c_142])).
% 8.97/3.03  tff(c_14303, plain, (![B_3163, B_3164]: (k1_funct_1(k1_xboole_0, B_3163)=B_3164)), inference(resolution, [status(thm)], [c_14207, c_14290])).
% 8.97/3.03  tff(c_14585, plain, (![C_43, B_3164]: (C_43=B_3164 | ~r2_hidden(C_43, k2_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_14303])).
% 8.97/3.03  tff(c_14716, plain, (![C_4050, B_4051]: (C_4050=B_4051)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_114, c_14207, c_8, c_14585])).
% 8.97/3.03  tff(c_15412, plain, (![B_4051]: (B_4051!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14716, c_53])).
% 8.97/3.03  tff(c_15724, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_15412])).
% 8.97/3.03  tff(c_15725, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_44])).
% 8.97/3.03  tff(c_14, plain, (![A_6]: (k1_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.97/3.03  tff(c_15771, plain, (![A_4742]: (k1_relat_1(A_4742)!='#skF_8' | A_4742='#skF_8' | ~v1_relat_1(A_4742))), inference(demodulation, [status(thm), theory('equality')], [c_15725, c_15725, c_14])).
% 8.97/3.03  tff(c_15774, plain, (![A_47, B_48]: (k1_relat_1('#skF_6'(A_47, B_48))!='#skF_8' | '#skF_6'(A_47, B_48)='#skF_8')), inference(resolution, [status(thm)], [c_40, c_15771])).
% 8.97/3.03  tff(c_15778, plain, (![A_4743, B_4744]: (A_4743!='#skF_8' | '#skF_6'(A_4743, B_4744)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_15774])).
% 8.97/3.03  tff(c_15788, plain, (![A_4743]: (v1_relat_1('#skF_8') | A_4743!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_15778, c_40])).
% 8.97/3.03  tff(c_15806, plain, (![A_4743]: (A_4743!='#skF_8')), inference(splitLeft, [status(thm)], [c_15788])).
% 8.97/3.03  tff(c_15728, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_15725, c_15725, c_10])).
% 8.97/3.03  tff(c_15817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15806, c_15728])).
% 8.97/3.03  tff(c_15818, plain, (v1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_15788])).
% 8.97/3.03  tff(c_15786, plain, (![A_4743]: (v1_funct_1('#skF_8') | A_4743!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_15778, c_38])).
% 8.97/3.03  tff(c_15795, plain, (![A_4743]: (A_4743!='#skF_8')), inference(splitLeft, [status(thm)], [c_15786])).
% 8.97/3.03  tff(c_15804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15795, c_15728])).
% 8.97/3.03  tff(c_15805, plain, (v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_15786])).
% 8.97/3.03  tff(c_15727, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_15725, c_15725, c_8])).
% 8.97/3.03  tff(c_15726, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_44])).
% 8.97/3.03  tff(c_15733, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_15725, c_15726])).
% 8.97/3.03  tff(c_15749, plain, (![C_4738]: (~r1_tarski(k2_relat_1(C_4738), '#skF_8') | k1_relat_1(C_4738)!='#skF_8' | ~v1_funct_1(C_4738) | ~v1_relat_1(C_4738))), inference(demodulation, [status(thm), theory('equality')], [c_15733, c_42])).
% 8.97/3.03  tff(c_15752, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_15727, c_15749])).
% 8.97/3.03  tff(c_15754, plain, (~r1_tarski('#skF_8', '#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15728, c_15752])).
% 8.97/3.03  tff(c_15834, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15818, c_15805, c_15754])).
% 8.97/3.03  tff(c_15856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15841, c_15834])).
% 8.97/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.97/3.03  
% 8.97/3.03  Inference rules
% 8.97/3.03  ----------------------
% 8.97/3.03  #Ref     : 4
% 8.97/3.03  #Sup     : 3182
% 8.97/3.03  #Fact    : 0
% 8.97/3.03  #Define  : 0
% 8.97/3.03  #Split   : 11
% 8.97/3.03  #Chain   : 0
% 8.97/3.03  #Close   : 0
% 8.97/3.03  
% 8.97/3.03  Ordering : KBO
% 8.97/3.03  
% 8.97/3.03  Simplification rules
% 8.97/3.03  ----------------------
% 8.97/3.03  #Subsume      : 1686
% 8.97/3.03  #Demod        : 2525
% 8.97/3.03  #Tautology    : 516
% 8.97/3.03  #SimpNegUnit  : 257
% 8.97/3.03  #BackRed      : 16
% 8.97/3.03  
% 8.97/3.03  #Partial instantiations: 2734
% 8.97/3.03  #Strategies tried      : 1
% 8.97/3.03  
% 8.97/3.03  Timing (in seconds)
% 8.97/3.03  ----------------------
% 8.97/3.03  Preprocessing        : 0.30
% 8.97/3.03  Parsing              : 0.16
% 8.97/3.03  CNF conversion       : 0.03
% 8.97/3.03  Main loop            : 1.96
% 8.97/3.03  Inferencing          : 0.71
% 8.97/3.03  Reduction            : 0.59
% 8.97/3.03  Demodulation         : 0.39
% 8.97/3.03  BG Simplification    : 0.06
% 8.97/3.03  Subsumption          : 0.51
% 8.97/3.03  Abstraction          : 0.12
% 8.97/3.03  MUC search           : 0.00
% 8.97/3.03  Cooper               : 0.00
% 8.97/3.03  Total                : 2.31
% 8.97/3.03  Index Insertion      : 0.00
% 8.97/3.03  Index Deletion       : 0.00
% 8.97/3.03  Index Matching       : 0.00
% 8.97/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
