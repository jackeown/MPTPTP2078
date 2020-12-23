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
% DateTime   : Thu Dec  3 10:10:33 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :  190 (2205 expanded)
%              Number of leaves         :   37 ( 786 expanded)
%              Depth                    :   27
%              Number of atoms          :  544 (6616 expanded)
%              Number of equality atoms :   51 (1040 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_133,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_150,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_131,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_142,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_116,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_146,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ( ! [C] :
                ( ( r2_hidden(C,k3_relat_1(A))
                  & r1_tarski(k1_wellord1(A,C),B) )
               => r2_hidden(C,B) )
           => r1_tarski(k3_relat_1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_wellord1)).

tff(f_46,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ( v2_wellord1(B)
          & r1_tarski(A,k3_relat_1(B)) )
       => ( ~ ( A != k3_relat_1(B)
              & ! [C] :
                  ~ ( r2_hidden(C,k3_relat_1(B))
                    & A = k1_wellord1(B,C) ) )
        <=> ! [C] :
              ( r2_hidden(C,A)
             => ! [D] :
                  ( r2_hidden(k4_tarski(D,C),B)
                 => r2_hidden(D,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_wellord1)).

tff(c_80,plain,(
    '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_86,plain,(
    v3_ordinal1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_84,plain,(
    v3_ordinal1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_72,plain,(
    ! [A_53] : v1_relat_1(k1_wellord2(A_53)) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_82,plain,(
    r4_wellord1(k1_wellord2('#skF_9'),k1_wellord2('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_125,plain,(
    ! [B_71,A_72] :
      ( r4_wellord1(B_71,A_72)
      | ~ r4_wellord1(A_72,B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_127,plain,
    ( r4_wellord1(k1_wellord2('#skF_10'),k1_wellord2('#skF_9'))
    | ~ v1_relat_1(k1_wellord2('#skF_10'))
    | ~ v1_relat_1(k1_wellord2('#skF_9')) ),
    inference(resolution,[status(thm)],[c_82,c_125])).

tff(c_130,plain,(
    r4_wellord1(k1_wellord2('#skF_10'),k1_wellord2('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_127])).

tff(c_78,plain,(
    ! [B_59,A_58] :
      ( k2_wellord1(k1_wellord2(B_59),A_58) = k1_wellord2(A_58)
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_66,plain,(
    ! [A_45] :
      ( k3_relat_1(k1_wellord2(A_45)) = A_45
      | ~ v1_relat_1(k1_wellord2(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_92,plain,(
    ! [A_45] : k3_relat_1(k1_wellord2(A_45)) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66])).

tff(c_74,plain,(
    ! [B_56,A_54] :
      ( k1_wellord1(k1_wellord2(B_56),A_54) = A_54
      | ~ r2_hidden(A_54,B_56)
      | ~ v3_ordinal1(B_56)
      | ~ v3_ordinal1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_262,plain,(
    ! [A_95,B_96] :
      ( ~ r4_wellord1(A_95,k2_wellord1(A_95,k1_wellord1(A_95,B_96)))
      | ~ r2_hidden(B_96,k3_relat_1(A_95))
      | ~ v2_wellord1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_265,plain,(
    ! [B_56,A_54] :
      ( ~ r4_wellord1(k1_wellord2(B_56),k2_wellord1(k1_wellord2(B_56),A_54))
      | ~ r2_hidden(A_54,k3_relat_1(k1_wellord2(B_56)))
      | ~ v2_wellord1(k1_wellord2(B_56))
      | ~ v1_relat_1(k1_wellord2(B_56))
      | ~ r2_hidden(A_54,B_56)
      | ~ v3_ordinal1(B_56)
      | ~ v3_ordinal1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_262])).

tff(c_379,plain,(
    ! [B_118,A_119] :
      ( ~ r4_wellord1(k1_wellord2(B_118),k2_wellord1(k1_wellord2(B_118),A_119))
      | ~ v2_wellord1(k1_wellord2(B_118))
      | ~ r2_hidden(A_119,B_118)
      | ~ v3_ordinal1(B_118)
      | ~ v3_ordinal1(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_92,c_265])).

tff(c_534,plain,(
    ! [B_132,A_133] :
      ( ~ r4_wellord1(k1_wellord2(B_132),k1_wellord2(A_133))
      | ~ v2_wellord1(k1_wellord2(B_132))
      | ~ r2_hidden(A_133,B_132)
      | ~ v3_ordinal1(B_132)
      | ~ v3_ordinal1(A_133)
      | ~ r1_tarski(A_133,B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_379])).

tff(c_537,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_10'))
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ v3_ordinal1('#skF_10')
    | ~ v3_ordinal1('#skF_9')
    | ~ r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_130,c_534])).

tff(c_543,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_10'))
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r1_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_537])).

tff(c_547,plain,(
    ~ r1_tarski('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_543])).

tff(c_76,plain,(
    ! [A_57] :
      ( v2_wellord1(k1_wellord2(A_57))
      | ~ v3_ordinal1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_540,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_9'))
    | ~ r2_hidden('#skF_10','#skF_9')
    | ~ v3_ordinal1('#skF_9')
    | ~ v3_ordinal1('#skF_10')
    | ~ r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_534])).

tff(c_546,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_9'))
    | ~ r2_hidden('#skF_10','#skF_9')
    | ~ r1_tarski('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_540])).

tff(c_548,plain,(
    ~ r1_tarski('#skF_10','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_232,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_6'(A_89,B_90),k3_relat_1(A_89))
      | r1_tarski(k3_relat_1(A_89),B_90)
      | ~ v2_wellord1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_239,plain,(
    ! [A_45,B_90] :
      ( r2_hidden('#skF_6'(k1_wellord2(A_45),B_90),A_45)
      | r1_tarski(k3_relat_1(k1_wellord2(A_45)),B_90)
      | ~ v2_wellord1(k1_wellord2(A_45))
      | ~ v1_relat_1(k1_wellord2(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_232])).

tff(c_243,plain,(
    ! [A_45,B_90] :
      ( r2_hidden('#skF_6'(k1_wellord2(A_45),B_90),A_45)
      | r1_tarski(A_45,B_90)
      | ~ v2_wellord1(k1_wellord2(A_45)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_92,c_239])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( r2_hidden(B_5,A_3)
      | B_5 = A_3
      | r2_hidden(A_3,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_269,plain,(
    ! [B_59,B_96] :
      ( ~ r4_wellord1(k1_wellord2(B_59),k1_wellord2(k1_wellord1(k1_wellord2(B_59),B_96)))
      | ~ r2_hidden(B_96,k3_relat_1(k1_wellord2(B_59)))
      | ~ v2_wellord1(k1_wellord2(B_59))
      | ~ v1_relat_1(k1_wellord2(B_59))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_59),B_96),B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_262])).

tff(c_685,plain,(
    ! [B_145,B_146] :
      ( ~ r4_wellord1(k1_wellord2(B_145),k1_wellord2(k1_wellord1(k1_wellord2(B_145),B_146)))
      | ~ r2_hidden(B_146,B_145)
      | ~ v2_wellord1(k1_wellord2(B_145))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_145),B_146),B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_92,c_269])).

tff(c_2232,plain,(
    ! [B_209,A_210] :
      ( ~ r4_wellord1(k1_wellord2(B_209),k1_wellord2(A_210))
      | ~ r2_hidden(A_210,B_209)
      | ~ v2_wellord1(k1_wellord2(B_209))
      | ~ r1_tarski(k1_wellord1(k1_wellord2(B_209),A_210),B_209)
      | ~ r2_hidden(A_210,B_209)
      | ~ v3_ordinal1(B_209)
      | ~ v3_ordinal1(A_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_685])).

tff(c_2236,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_9'))
    | ~ r1_tarski(k1_wellord1(k1_wellord2('#skF_9'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_10','#skF_9')
    | ~ v3_ordinal1('#skF_9')
    | ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_82,c_2232])).

tff(c_2242,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_9'))
    | ~ r1_tarski(k1_wellord1(k1_wellord2('#skF_9'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_2236])).

tff(c_2243,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2242])).

tff(c_2255,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10')
    | ~ v3_ordinal1('#skF_10')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_8,c_2243])).

tff(c_2272,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_2255])).

tff(c_2273,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2272])).

tff(c_12,plain,(
    ! [D_17,B_13,A_6] :
      ( r2_hidden(k4_tarski(D_17,B_13),A_6)
      | ~ r2_hidden(D_17,k1_wellord1(A_6,B_13))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [D_31,B_19,C_29] :
      ( r2_hidden(D_31,k3_relat_1(B_19))
      | ~ r2_hidden(k4_tarski(D_31,C_29),B_19)
      | ~ r2_hidden(C_29,k3_relat_1(B_19))
      | ~ r1_tarski(k3_relat_1(B_19),k3_relat_1(B_19))
      | ~ v2_wellord1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_342,plain,(
    ! [D_112,B_113,C_114] :
      ( r2_hidden(D_112,k3_relat_1(B_113))
      | ~ r2_hidden(k4_tarski(D_112,C_114),B_113)
      | ~ r2_hidden(C_114,k3_relat_1(B_113))
      | ~ v2_wellord1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_42])).

tff(c_383,plain,(
    ! [D_120,A_121,B_122] :
      ( r2_hidden(D_120,k3_relat_1(A_121))
      | ~ r2_hidden(B_122,k3_relat_1(A_121))
      | ~ v2_wellord1(A_121)
      | ~ r2_hidden(D_120,k1_wellord1(A_121,B_122))
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_12,c_342])).

tff(c_406,plain,(
    ! [D_120,A_45,B_122] :
      ( r2_hidden(D_120,k3_relat_1(k1_wellord2(A_45)))
      | ~ r2_hidden(B_122,A_45)
      | ~ v2_wellord1(k1_wellord2(A_45))
      | ~ r2_hidden(D_120,k1_wellord1(k1_wellord2(A_45),B_122))
      | ~ v1_relat_1(k1_wellord2(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_383])).

tff(c_417,plain,(
    ! [D_123,A_124,B_125] :
      ( r2_hidden(D_123,A_124)
      | ~ r2_hidden(B_125,A_124)
      | ~ v2_wellord1(k1_wellord2(A_124))
      | ~ r2_hidden(D_123,k1_wellord1(k1_wellord2(A_124),B_125)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_92,c_406])).

tff(c_440,plain,(
    ! [D_123,B_56,A_54] :
      ( r2_hidden(D_123,B_56)
      | ~ r2_hidden(A_54,B_56)
      | ~ v2_wellord1(k1_wellord2(B_56))
      | ~ r2_hidden(D_123,A_54)
      | ~ r2_hidden(A_54,B_56)
      | ~ v3_ordinal1(B_56)
      | ~ v3_ordinal1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_417])).

tff(c_2287,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,'#skF_10')
      | ~ v2_wellord1(k1_wellord2('#skF_10'))
      | ~ r2_hidden(D_123,'#skF_9')
      | ~ r2_hidden('#skF_9','#skF_10')
      | ~ v3_ordinal1('#skF_10')
      | ~ v3_ordinal1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2273,c_440])).

tff(c_2304,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,'#skF_10')
      | ~ v2_wellord1(k1_wellord2('#skF_10'))
      | ~ r2_hidden(D_123,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_2273,c_2287])).

tff(c_2309,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_2304])).

tff(c_2312,plain,(
    ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_2309])).

tff(c_2316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2312])).

tff(c_2317,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,'#skF_10')
      | ~ r2_hidden(D_123,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_2304])).

tff(c_70,plain,(
    ! [C_51,D_52,A_45] :
      ( r1_tarski(C_51,D_52)
      | ~ r2_hidden(k4_tarski(C_51,D_52),k1_wellord2(A_45))
      | ~ r2_hidden(D_52,A_45)
      | ~ r2_hidden(C_51,A_45)
      | ~ v1_relat_1(k1_wellord2(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_281,plain,(
    ! [C_100,D_101,A_102] :
      ( r1_tarski(C_100,D_101)
      | ~ r2_hidden(k4_tarski(C_100,D_101),k1_wellord2(A_102))
      | ~ r2_hidden(D_101,A_102)
      | ~ r2_hidden(C_100,A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70])).

tff(c_288,plain,(
    ! [D_17,B_13,A_102] :
      ( r1_tarski(D_17,B_13)
      | ~ r2_hidden(B_13,A_102)
      | ~ r2_hidden(D_17,A_102)
      | ~ r2_hidden(D_17,k1_wellord1(k1_wellord2(A_102),B_13))
      | ~ v1_relat_1(k1_wellord2(A_102)) ) ),
    inference(resolution,[status(thm)],[c_12,c_281])).

tff(c_301,plain,(
    ! [D_103,B_104,A_105] :
      ( r1_tarski(D_103,B_104)
      | ~ r2_hidden(B_104,A_105)
      | ~ r2_hidden(D_103,A_105)
      | ~ r2_hidden(D_103,k1_wellord1(k1_wellord2(A_105),B_104)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_288])).

tff(c_320,plain,(
    ! [D_103,A_54,B_56] :
      ( r1_tarski(D_103,A_54)
      | ~ r2_hidden(A_54,B_56)
      | ~ r2_hidden(D_103,B_56)
      | ~ r2_hidden(D_103,A_54)
      | ~ r2_hidden(A_54,B_56)
      | ~ v3_ordinal1(B_56)
      | ~ v3_ordinal1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_301])).

tff(c_2289,plain,(
    ! [D_103] :
      ( r1_tarski(D_103,'#skF_9')
      | ~ r2_hidden(D_103,'#skF_10')
      | ~ r2_hidden(D_103,'#skF_9')
      | ~ r2_hidden('#skF_9','#skF_10')
      | ~ v3_ordinal1('#skF_10')
      | ~ v3_ordinal1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2273,c_320])).

tff(c_2467,plain,(
    ! [D_213] :
      ( r1_tarski(D_213,'#skF_9')
      | ~ r2_hidden(D_213,'#skF_10')
      | ~ r2_hidden(D_213,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_2273,c_2289])).

tff(c_2698,plain,(
    ! [D_215] :
      ( r1_tarski(D_215,'#skF_9')
      | ~ r2_hidden(D_215,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2317,c_2467])).

tff(c_2779,plain,(
    ! [B_90] :
      ( r1_tarski('#skF_6'(k1_wellord2('#skF_9'),B_90),'#skF_9')
      | r1_tarski('#skF_9',B_90)
      | ~ v2_wellord1(k1_wellord2('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_243,c_2698])).

tff(c_3221,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_2779])).

tff(c_3224,plain,(
    ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_3221])).

tff(c_3228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3224])).

tff(c_3230,plain,(
    v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2779])).

tff(c_2382,plain,(
    ! [D_212] :
      ( r2_hidden(D_212,'#skF_10')
      | ~ r2_hidden(D_212,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_2304])).

tff(c_44,plain,(
    ! [A_33,B_37] :
      ( ~ r2_hidden('#skF_6'(A_33,B_37),B_37)
      | r1_tarski(k3_relat_1(A_33),B_37)
      | ~ v2_wellord1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3316,plain,(
    ! [A_224] :
      ( r1_tarski(k3_relat_1(A_224),'#skF_10')
      | ~ v2_wellord1(A_224)
      | ~ v1_relat_1(A_224)
      | ~ r2_hidden('#skF_6'(A_224,'#skF_10'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2382,c_44])).

tff(c_3329,plain,
    ( r1_tarski(k3_relat_1(k1_wellord2('#skF_9')),'#skF_10')
    | ~ v1_relat_1(k1_wellord2('#skF_9'))
    | r1_tarski('#skF_9','#skF_10')
    | ~ v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(resolution,[status(thm)],[c_243,c_3316])).

tff(c_3347,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_72,c_92,c_3329])).

tff(c_3349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_3347])).

tff(c_3350,plain,
    ( ~ r1_tarski(k1_wellord1(k1_wellord2('#skF_9'),'#skF_10'),'#skF_9')
    | ~ v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_2242])).

tff(c_3382,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_3350])).

tff(c_3385,plain,(
    ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_3382])).

tff(c_3389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3385])).

tff(c_3391,plain,(
    v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_3350])).

tff(c_3351,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2242])).

tff(c_3361,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,'#skF_9')
      | ~ v2_wellord1(k1_wellord2('#skF_9'))
      | ~ r2_hidden(D_123,'#skF_10')
      | ~ r2_hidden('#skF_10','#skF_9')
      | ~ v3_ordinal1('#skF_9')
      | ~ v3_ordinal1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_3351,c_440])).

tff(c_3378,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,'#skF_9')
      | ~ v2_wellord1(k1_wellord2('#skF_9'))
      | ~ r2_hidden(D_123,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_3351,c_3361])).

tff(c_3399,plain,(
    ! [D_225] :
      ( r2_hidden(D_225,'#skF_9')
      | ~ r2_hidden(D_225,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3391,c_3378])).

tff(c_3478,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_6'(k1_wellord2('#skF_10'),B_90),'#skF_9')
      | r1_tarski('#skF_10',B_90)
      | ~ v2_wellord1(k1_wellord2('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_243,c_3399])).

tff(c_3901,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_3478])).

tff(c_3904,plain,(
    ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_3901])).

tff(c_3908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3904])).

tff(c_3910,plain,(
    v2_wellord1(k1_wellord2('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_3478])).

tff(c_3988,plain,(
    ! [B_231] :
      ( r2_hidden('#skF_6'(k1_wellord2('#skF_10'),B_231),'#skF_9')
      | r1_tarski('#skF_10',B_231) ) ),
    inference(splitRight,[status(thm)],[c_3478])).

tff(c_4004,plain,
    ( r1_tarski(k3_relat_1(k1_wellord2('#skF_10')),'#skF_9')
    | ~ v2_wellord1(k1_wellord2('#skF_10'))
    | ~ v1_relat_1(k1_wellord2('#skF_10'))
    | r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_3988,c_44])).

tff(c_4025,plain,(
    r1_tarski('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3910,c_92,c_4004])).

tff(c_4027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_548,c_4025])).

tff(c_4028,plain,
    ( ~ r2_hidden('#skF_10','#skF_9')
    | ~ v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_4034,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_4028])).

tff(c_4037,plain,(
    ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_4034])).

tff(c_4041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4037])).

tff(c_4043,plain,(
    v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_4028])).

tff(c_4042,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_4028])).

tff(c_4046,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10')
    | ~ v3_ordinal1('#skF_10')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_8,c_4042])).

tff(c_4052,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_4046])).

tff(c_4053,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4052])).

tff(c_4119,plain,(
    ! [D_234,A_235,B_236] :
      ( r1_tarski(D_234,A_235)
      | ~ r2_hidden(A_235,B_236)
      | ~ r2_hidden(D_234,B_236)
      | ~ r2_hidden(D_234,A_235)
      | ~ r2_hidden(A_235,B_236)
      | ~ v3_ordinal1(B_236)
      | ~ v3_ordinal1(A_235) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_301])).

tff(c_4123,plain,(
    ! [D_234] :
      ( r1_tarski(D_234,'#skF_9')
      | ~ r2_hidden(D_234,'#skF_10')
      | ~ r2_hidden(D_234,'#skF_9')
      | ~ r2_hidden('#skF_9','#skF_10')
      | ~ v3_ordinal1('#skF_10')
      | ~ v3_ordinal1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4053,c_4119])).

tff(c_4164,plain,(
    ! [D_237] :
      ( r1_tarski(D_237,'#skF_9')
      | ~ r2_hidden(D_237,'#skF_10')
      | ~ r2_hidden(D_237,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_4053,c_4123])).

tff(c_4203,plain,(
    ! [B_90] :
      ( r1_tarski('#skF_6'(k1_wellord2('#skF_10'),B_90),'#skF_9')
      | ~ r2_hidden('#skF_6'(k1_wellord2('#skF_10'),B_90),'#skF_9')
      | r1_tarski('#skF_10',B_90)
      | ~ v2_wellord1(k1_wellord2('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_243,c_4164])).

tff(c_4310,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_4203])).

tff(c_4326,plain,(
    ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_4310])).

tff(c_4330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4326])).

tff(c_4332,plain,(
    v2_wellord1(k1_wellord2('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_4203])).

tff(c_4418,plain,(
    ! [D_248,B_249,A_250] :
      ( r2_hidden(D_248,B_249)
      | ~ r2_hidden(A_250,B_249)
      | ~ v2_wellord1(k1_wellord2(B_249))
      | ~ r2_hidden(D_248,A_250)
      | ~ r2_hidden(A_250,B_249)
      | ~ v3_ordinal1(B_249)
      | ~ v3_ordinal1(A_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_417])).

tff(c_4424,plain,(
    ! [D_248] :
      ( r2_hidden(D_248,'#skF_10')
      | ~ v2_wellord1(k1_wellord2('#skF_10'))
      | ~ r2_hidden(D_248,'#skF_9')
      | ~ r2_hidden('#skF_9','#skF_10')
      | ~ v3_ordinal1('#skF_10')
      | ~ v3_ordinal1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4053,c_4418])).

tff(c_4468,plain,(
    ! [D_251] :
      ( r2_hidden(D_251,'#skF_10')
      | ~ r2_hidden(D_251,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_4053,c_4332,c_4424])).

tff(c_4639,plain,(
    ! [A_257] :
      ( r1_tarski(k3_relat_1(A_257),'#skF_10')
      | ~ v2_wellord1(A_257)
      | ~ v1_relat_1(A_257)
      | ~ r2_hidden('#skF_6'(A_257,'#skF_10'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4468,c_44])).

tff(c_4643,plain,
    ( r1_tarski(k3_relat_1(k1_wellord2('#skF_9')),'#skF_10')
    | ~ v1_relat_1(k1_wellord2('#skF_9'))
    | r1_tarski('#skF_9','#skF_10')
    | ~ v2_wellord1(k1_wellord2('#skF_9')) ),
    inference(resolution,[status(thm)],[c_243,c_4639])).

tff(c_4652,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4043,c_72,c_92,c_4643])).

tff(c_4654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_4652])).

tff(c_4656,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_543])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4658,plain,
    ( '#skF_10' = '#skF_9'
    | ~ r1_tarski('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_4656,c_2])).

tff(c_4661,plain,(
    ~ r1_tarski('#skF_10','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4658])).

tff(c_4655,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | ~ v2_wellord1(k1_wellord2('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_543])).

tff(c_4662,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_4655])).

tff(c_4665,plain,(
    ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_4662])).

tff(c_4669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4665])).

tff(c_4671,plain,(
    v2_wellord1(k1_wellord2('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_4655])).

tff(c_4862,plain,(
    ! [D_268,B_269,A_270] :
      ( r2_hidden(D_268,B_269)
      | ~ r2_hidden(A_270,B_269)
      | ~ v2_wellord1(k1_wellord2(B_269))
      | ~ r2_hidden(D_268,A_270)
      | ~ r2_hidden(A_270,B_269)
      | ~ v3_ordinal1(B_269)
      | ~ v3_ordinal1(A_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_417])).

tff(c_5254,plain,(
    ! [D_291,A_292,B_293] :
      ( r2_hidden(D_291,A_292)
      | ~ v2_wellord1(k1_wellord2(A_292))
      | ~ r2_hidden(D_291,B_293)
      | ~ r2_hidden(B_293,A_292)
      | B_293 = A_292
      | r2_hidden(A_292,B_293)
      | ~ v3_ordinal1(B_293)
      | ~ v3_ordinal1(A_292) ) ),
    inference(resolution,[status(thm)],[c_8,c_4862])).

tff(c_5256,plain,(
    ! [D_291,B_293] :
      ( r2_hidden(D_291,'#skF_10')
      | ~ r2_hidden(D_291,B_293)
      | ~ r2_hidden(B_293,'#skF_10')
      | B_293 = '#skF_10'
      | r2_hidden('#skF_10',B_293)
      | ~ v3_ordinal1(B_293)
      | ~ v3_ordinal1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_4671,c_5254])).

tff(c_5263,plain,(
    ! [D_294,B_295] :
      ( r2_hidden(D_294,'#skF_10')
      | ~ r2_hidden(D_294,B_295)
      | ~ r2_hidden(B_295,'#skF_10')
      | B_295 = '#skF_10'
      | r2_hidden('#skF_10',B_295)
      | ~ v3_ordinal1(B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5256])).

tff(c_5395,plain,(
    ! [B_302,A_303] :
      ( r2_hidden(B_302,'#skF_10')
      | ~ r2_hidden(A_303,'#skF_10')
      | A_303 = '#skF_10'
      | r2_hidden('#skF_10',A_303)
      | B_302 = A_303
      | r2_hidden(A_303,B_302)
      | ~ v3_ordinal1(B_302)
      | ~ v3_ordinal1(A_303) ) ),
    inference(resolution,[status(thm)],[c_8,c_5263])).

tff(c_5419,plain,(
    ! [B_302,B_5] :
      ( r2_hidden(B_302,'#skF_10')
      | B_5 = B_302
      | r2_hidden(B_5,B_302)
      | ~ v3_ordinal1(B_302)
      | B_5 = '#skF_10'
      | r2_hidden('#skF_10',B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_8,c_5395])).

tff(c_5497,plain,(
    ! [B_304,B_305] :
      ( r2_hidden(B_304,'#skF_10')
      | B_305 = B_304
      | r2_hidden(B_305,B_304)
      | ~ v3_ordinal1(B_304)
      | B_305 = '#skF_10'
      | r2_hidden('#skF_10',B_305)
      | ~ v3_ordinal1(B_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5419])).

tff(c_136,plain,(
    ! [B_73,A_74] :
      ( k1_wellord1(k1_wellord2(B_73),A_74) = A_74
      | ~ r2_hidden(A_74,B_73)
      | ~ v3_ordinal1(B_73)
      | ~ v3_ordinal1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_14,plain,(
    ! [D_17,A_6] :
      ( ~ r2_hidden(D_17,k1_wellord1(A_6,D_17))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_142,plain,(
    ! [A_74,B_73] :
      ( ~ r2_hidden(A_74,A_74)
      | ~ v1_relat_1(k1_wellord2(B_73))
      | ~ r2_hidden(A_74,B_73)
      | ~ v3_ordinal1(B_73)
      | ~ v3_ordinal1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_14])).

tff(c_148,plain,(
    ! [A_74,B_73] :
      ( ~ r2_hidden(A_74,A_74)
      | ~ r2_hidden(A_74,B_73)
      | ~ v3_ordinal1(B_73)
      | ~ v3_ordinal1(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_142])).

tff(c_5539,plain,(
    ! [B_73,B_305] :
      ( ~ r2_hidden('#skF_10',B_73)
      | ~ v3_ordinal1(B_73)
      | r2_hidden(B_305,'#skF_10')
      | ~ v3_ordinal1('#skF_10')
      | B_305 = '#skF_10'
      | r2_hidden('#skF_10',B_305)
      | ~ v3_ordinal1(B_305) ) ),
    inference(resolution,[status(thm)],[c_5497,c_148])).

tff(c_5673,plain,(
    ! [B_73,B_305] :
      ( ~ r2_hidden('#skF_10',B_73)
      | ~ v3_ordinal1(B_73)
      | r2_hidden(B_305,'#skF_10')
      | B_305 = '#skF_10'
      | r2_hidden('#skF_10',B_305)
      | ~ v3_ordinal1(B_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5539])).

tff(c_5715,plain,(
    ! [B_306] :
      ( ~ r2_hidden('#skF_10',B_306)
      | ~ v3_ordinal1(B_306) ) ),
    inference(splitLeft,[status(thm)],[c_5673])).

tff(c_5734,plain,(
    ! [A_3] :
      ( A_3 = '#skF_10'
      | r2_hidden(A_3,'#skF_10')
      | ~ v3_ordinal1('#skF_10')
      | ~ v3_ordinal1(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_5715])).

tff(c_5754,plain,(
    ! [A_307] :
      ( A_307 = '#skF_10'
      | r2_hidden(A_307,'#skF_10')
      | ~ v3_ordinal1(A_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5734])).

tff(c_4670,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_4655])).

tff(c_5783,plain,
    ( '#skF_10' = '#skF_9'
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_5754,c_4670])).

tff(c_5830,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_5783])).

tff(c_5832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_5830])).

tff(c_5833,plain,(
    ! [B_305] :
      ( r2_hidden(B_305,'#skF_10')
      | B_305 = '#skF_10'
      | r2_hidden('#skF_10',B_305)
      | ~ v3_ordinal1(B_305) ) ),
    inference(splitRight,[status(thm)],[c_5673])).

tff(c_5854,plain,(
    ! [B_308] :
      ( r2_hidden(B_308,'#skF_10')
      | B_308 = '#skF_10'
      | r2_hidden('#skF_10',B_308)
      | ~ v3_ordinal1(B_308) ) ),
    inference(splitRight,[status(thm)],[c_5673])).

tff(c_5908,plain,(
    ! [D_123,B_308] :
      ( r2_hidden(D_123,B_308)
      | ~ v2_wellord1(k1_wellord2(B_308))
      | ~ r2_hidden(D_123,'#skF_10')
      | ~ r2_hidden('#skF_10',B_308)
      | ~ v3_ordinal1('#skF_10')
      | r2_hidden(B_308,'#skF_10')
      | B_308 = '#skF_10'
      | ~ v3_ordinal1(B_308) ) ),
    inference(resolution,[status(thm)],[c_5854,c_440])).

tff(c_6046,plain,(
    ! [D_314,B_315] :
      ( r2_hidden(D_314,B_315)
      | ~ v2_wellord1(k1_wellord2(B_315))
      | ~ r2_hidden(D_314,'#skF_10')
      | ~ r2_hidden('#skF_10',B_315)
      | r2_hidden(B_315,'#skF_10')
      | B_315 = '#skF_10'
      | ~ v3_ordinal1(B_315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5908])).

tff(c_6056,plain,(
    ! [D_316,A_317] :
      ( r2_hidden(D_316,A_317)
      | ~ r2_hidden(D_316,'#skF_10')
      | ~ r2_hidden('#skF_10',A_317)
      | r2_hidden(A_317,'#skF_10')
      | A_317 = '#skF_10'
      | ~ v3_ordinal1(A_317) ) ),
    inference(resolution,[status(thm)],[c_76,c_6046])).

tff(c_6085,plain,(
    ! [B_90,A_317] :
      ( r2_hidden('#skF_6'(k1_wellord2('#skF_10'),B_90),A_317)
      | ~ r2_hidden('#skF_10',A_317)
      | r2_hidden(A_317,'#skF_10')
      | A_317 = '#skF_10'
      | ~ v3_ordinal1(A_317)
      | r1_tarski('#skF_10',B_90)
      | ~ v2_wellord1(k1_wellord2('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_243,c_6056])).

tff(c_6192,plain,(
    ! [B_320,A_321] :
      ( r2_hidden('#skF_6'(k1_wellord2('#skF_10'),B_320),A_321)
      | ~ r2_hidden('#skF_10',A_321)
      | r2_hidden(A_321,'#skF_10')
      | A_321 = '#skF_10'
      | ~ v3_ordinal1(A_321)
      | r1_tarski('#skF_10',B_320) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4671,c_6085])).

tff(c_6243,plain,(
    ! [A_321] :
      ( r1_tarski(k3_relat_1(k1_wellord2('#skF_10')),A_321)
      | ~ v2_wellord1(k1_wellord2('#skF_10'))
      | ~ v1_relat_1(k1_wellord2('#skF_10'))
      | ~ r2_hidden('#skF_10',A_321)
      | r2_hidden(A_321,'#skF_10')
      | A_321 = '#skF_10'
      | ~ v3_ordinal1(A_321)
      | r1_tarski('#skF_10',A_321) ) ),
    inference(resolution,[status(thm)],[c_6192,c_44])).

tff(c_6277,plain,(
    ! [A_322] :
      ( ~ r2_hidden('#skF_10',A_322)
      | r2_hidden(A_322,'#skF_10')
      | A_322 = '#skF_10'
      | ~ v3_ordinal1(A_322)
      | r1_tarski('#skF_10',A_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4671,c_92,c_6243])).

tff(c_6314,plain,(
    ! [B_323] :
      ( r1_tarski('#skF_10',B_323)
      | r2_hidden(B_323,'#skF_10')
      | B_323 = '#skF_10'
      | ~ v3_ordinal1(B_323) ) ),
    inference(resolution,[status(thm)],[c_5833,c_6277])).

tff(c_6348,plain,
    ( r1_tarski('#skF_10','#skF_9')
    | '#skF_10' = '#skF_9'
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_6314,c_4670])).

tff(c_6398,plain,
    ( r1_tarski('#skF_10','#skF_9')
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6348])).

tff(c_6400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4661,c_6398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.66/2.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/2.54  
% 7.81/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.54  %$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_7 > #skF_5 > #skF_4
% 7.82/2.54  
% 7.82/2.54  %Foreground sorts:
% 7.82/2.54  
% 7.82/2.54  
% 7.82/2.54  %Background operators:
% 7.82/2.54  
% 7.82/2.54  
% 7.82/2.54  %Foreground operators:
% 7.82/2.54  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.82/2.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.82/2.54  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 7.82/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.82/2.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.82/2.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.82/2.54  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 7.82/2.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.82/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.82/2.54  tff('#skF_10', type, '#skF_10': $i).
% 7.82/2.54  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 7.82/2.54  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 7.82/2.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.82/2.54  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.82/2.54  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 7.82/2.54  tff('#skF_9', type, '#skF_9': $i).
% 7.82/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.82/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.82/2.54  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 7.82/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.82/2.54  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.82/2.54  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 7.82/2.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.82/2.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.82/2.54  
% 7.82/2.57  tff(f_160, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 7.82/2.57  tff(f_133, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 7.82/2.57  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 7.82/2.57  tff(f_150, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 7.82/2.57  tff(f_131, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 7.82/2.57  tff(f_142, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 7.82/2.57  tff(f_116, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 7.82/2.57  tff(f_146, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 7.82/2.57  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ((![C]: ((r2_hidden(C, k3_relat_1(A)) & r1_tarski(k1_wellord1(A, C), B)) => r2_hidden(C, B))) => r1_tarski(k3_relat_1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_wellord1)).
% 7.82/2.57  tff(f_46, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 7.82/2.57  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 7.82/2.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.82/2.57  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => ((v2_wellord1(B) & r1_tarski(A, k3_relat_1(B))) => (~(~(A = k3_relat_1(B)) & (![C]: ~(r2_hidden(C, k3_relat_1(B)) & (A = k1_wellord1(B, C))))) <=> (![C]: (r2_hidden(C, A) => (![D]: (r2_hidden(k4_tarski(D, C), B) => r2_hidden(D, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_wellord1)).
% 7.82/2.57  tff(c_80, plain, ('#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.82/2.57  tff(c_86, plain, (v3_ordinal1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.82/2.57  tff(c_84, plain, (v3_ordinal1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.82/2.57  tff(c_72, plain, (![A_53]: (v1_relat_1(k1_wellord2(A_53)))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.82/2.57  tff(c_82, plain, (r4_wellord1(k1_wellord2('#skF_9'), k1_wellord2('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.82/2.57  tff(c_125, plain, (![B_71, A_72]: (r4_wellord1(B_71, A_72) | ~r4_wellord1(A_72, B_71) | ~v1_relat_1(B_71) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.82/2.57  tff(c_127, plain, (r4_wellord1(k1_wellord2('#skF_10'), k1_wellord2('#skF_9')) | ~v1_relat_1(k1_wellord2('#skF_10')) | ~v1_relat_1(k1_wellord2('#skF_9'))), inference(resolution, [status(thm)], [c_82, c_125])).
% 7.82/2.57  tff(c_130, plain, (r4_wellord1(k1_wellord2('#skF_10'), k1_wellord2('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_127])).
% 7.82/2.57  tff(c_78, plain, (![B_59, A_58]: (k2_wellord1(k1_wellord2(B_59), A_58)=k1_wellord2(A_58) | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.82/2.57  tff(c_66, plain, (![A_45]: (k3_relat_1(k1_wellord2(A_45))=A_45 | ~v1_relat_1(k1_wellord2(A_45)))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.82/2.57  tff(c_92, plain, (![A_45]: (k3_relat_1(k1_wellord2(A_45))=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66])).
% 7.82/2.57  tff(c_74, plain, (![B_56, A_54]: (k1_wellord1(k1_wellord2(B_56), A_54)=A_54 | ~r2_hidden(A_54, B_56) | ~v3_ordinal1(B_56) | ~v3_ordinal1(A_54))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.82/2.57  tff(c_262, plain, (![A_95, B_96]: (~r4_wellord1(A_95, k2_wellord1(A_95, k1_wellord1(A_95, B_96))) | ~r2_hidden(B_96, k3_relat_1(A_95)) | ~v2_wellord1(A_95) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.82/2.57  tff(c_265, plain, (![B_56, A_54]: (~r4_wellord1(k1_wellord2(B_56), k2_wellord1(k1_wellord2(B_56), A_54)) | ~r2_hidden(A_54, k3_relat_1(k1_wellord2(B_56))) | ~v2_wellord1(k1_wellord2(B_56)) | ~v1_relat_1(k1_wellord2(B_56)) | ~r2_hidden(A_54, B_56) | ~v3_ordinal1(B_56) | ~v3_ordinal1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_74, c_262])).
% 7.82/2.57  tff(c_379, plain, (![B_118, A_119]: (~r4_wellord1(k1_wellord2(B_118), k2_wellord1(k1_wellord2(B_118), A_119)) | ~v2_wellord1(k1_wellord2(B_118)) | ~r2_hidden(A_119, B_118) | ~v3_ordinal1(B_118) | ~v3_ordinal1(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_92, c_265])).
% 7.82/2.57  tff(c_534, plain, (![B_132, A_133]: (~r4_wellord1(k1_wellord2(B_132), k1_wellord2(A_133)) | ~v2_wellord1(k1_wellord2(B_132)) | ~r2_hidden(A_133, B_132) | ~v3_ordinal1(B_132) | ~v3_ordinal1(A_133) | ~r1_tarski(A_133, B_132))), inference(superposition, [status(thm), theory('equality')], [c_78, c_379])).
% 7.82/2.57  tff(c_537, plain, (~v2_wellord1(k1_wellord2('#skF_10')) | ~r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1('#skF_9') | ~r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_130, c_534])).
% 7.82/2.57  tff(c_543, plain, (~v2_wellord1(k1_wellord2('#skF_10')) | ~r2_hidden('#skF_9', '#skF_10') | ~r1_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_537])).
% 7.82/2.57  tff(c_547, plain, (~r1_tarski('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_543])).
% 7.82/2.57  tff(c_76, plain, (![A_57]: (v2_wellord1(k1_wellord2(A_57)) | ~v3_ordinal1(A_57))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.82/2.57  tff(c_540, plain, (~v2_wellord1(k1_wellord2('#skF_9')) | ~r2_hidden('#skF_10', '#skF_9') | ~v3_ordinal1('#skF_9') | ~v3_ordinal1('#skF_10') | ~r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_82, c_534])).
% 7.82/2.57  tff(c_546, plain, (~v2_wellord1(k1_wellord2('#skF_9')) | ~r2_hidden('#skF_10', '#skF_9') | ~r1_tarski('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_540])).
% 7.82/2.57  tff(c_548, plain, (~r1_tarski('#skF_10', '#skF_9')), inference(splitLeft, [status(thm)], [c_546])).
% 7.82/2.57  tff(c_232, plain, (![A_89, B_90]: (r2_hidden('#skF_6'(A_89, B_90), k3_relat_1(A_89)) | r1_tarski(k3_relat_1(A_89), B_90) | ~v2_wellord1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.82/2.57  tff(c_239, plain, (![A_45, B_90]: (r2_hidden('#skF_6'(k1_wellord2(A_45), B_90), A_45) | r1_tarski(k3_relat_1(k1_wellord2(A_45)), B_90) | ~v2_wellord1(k1_wellord2(A_45)) | ~v1_relat_1(k1_wellord2(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_232])).
% 7.82/2.57  tff(c_243, plain, (![A_45, B_90]: (r2_hidden('#skF_6'(k1_wellord2(A_45), B_90), A_45) | r1_tarski(A_45, B_90) | ~v2_wellord1(k1_wellord2(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_92, c_239])).
% 7.82/2.57  tff(c_8, plain, (![B_5, A_3]: (r2_hidden(B_5, A_3) | B_5=A_3 | r2_hidden(A_3, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.82/2.57  tff(c_269, plain, (![B_59, B_96]: (~r4_wellord1(k1_wellord2(B_59), k1_wellord2(k1_wellord1(k1_wellord2(B_59), B_96))) | ~r2_hidden(B_96, k3_relat_1(k1_wellord2(B_59))) | ~v2_wellord1(k1_wellord2(B_59)) | ~v1_relat_1(k1_wellord2(B_59)) | ~r1_tarski(k1_wellord1(k1_wellord2(B_59), B_96), B_59))), inference(superposition, [status(thm), theory('equality')], [c_78, c_262])).
% 7.82/2.57  tff(c_685, plain, (![B_145, B_146]: (~r4_wellord1(k1_wellord2(B_145), k1_wellord2(k1_wellord1(k1_wellord2(B_145), B_146))) | ~r2_hidden(B_146, B_145) | ~v2_wellord1(k1_wellord2(B_145)) | ~r1_tarski(k1_wellord1(k1_wellord2(B_145), B_146), B_145))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_92, c_269])).
% 7.82/2.57  tff(c_2232, plain, (![B_209, A_210]: (~r4_wellord1(k1_wellord2(B_209), k1_wellord2(A_210)) | ~r2_hidden(A_210, B_209) | ~v2_wellord1(k1_wellord2(B_209)) | ~r1_tarski(k1_wellord1(k1_wellord2(B_209), A_210), B_209) | ~r2_hidden(A_210, B_209) | ~v3_ordinal1(B_209) | ~v3_ordinal1(A_210))), inference(superposition, [status(thm), theory('equality')], [c_74, c_685])).
% 7.82/2.57  tff(c_2236, plain, (~v2_wellord1(k1_wellord2('#skF_9')) | ~r1_tarski(k1_wellord1(k1_wellord2('#skF_9'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_10', '#skF_9') | ~v3_ordinal1('#skF_9') | ~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_82, c_2232])).
% 7.82/2.57  tff(c_2242, plain, (~v2_wellord1(k1_wellord2('#skF_9')) | ~r1_tarski(k1_wellord1(k1_wellord2('#skF_9'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_2236])).
% 7.82/2.57  tff(c_2243, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(splitLeft, [status(thm)], [c_2242])).
% 7.82/2.57  tff(c_2255, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_8, c_2243])).
% 7.82/2.57  tff(c_2272, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_2255])).
% 7.82/2.57  tff(c_2273, plain, (r2_hidden('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_80, c_2272])).
% 7.82/2.57  tff(c_12, plain, (![D_17, B_13, A_6]: (r2_hidden(k4_tarski(D_17, B_13), A_6) | ~r2_hidden(D_17, k1_wellord1(A_6, B_13)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.82/2.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.82/2.57  tff(c_42, plain, (![D_31, B_19, C_29]: (r2_hidden(D_31, k3_relat_1(B_19)) | ~r2_hidden(k4_tarski(D_31, C_29), B_19) | ~r2_hidden(C_29, k3_relat_1(B_19)) | ~r1_tarski(k3_relat_1(B_19), k3_relat_1(B_19)) | ~v2_wellord1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.82/2.57  tff(c_342, plain, (![D_112, B_113, C_114]: (r2_hidden(D_112, k3_relat_1(B_113)) | ~r2_hidden(k4_tarski(D_112, C_114), B_113) | ~r2_hidden(C_114, k3_relat_1(B_113)) | ~v2_wellord1(B_113) | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_42])).
% 7.82/2.57  tff(c_383, plain, (![D_120, A_121, B_122]: (r2_hidden(D_120, k3_relat_1(A_121)) | ~r2_hidden(B_122, k3_relat_1(A_121)) | ~v2_wellord1(A_121) | ~r2_hidden(D_120, k1_wellord1(A_121, B_122)) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_12, c_342])).
% 7.82/2.57  tff(c_406, plain, (![D_120, A_45, B_122]: (r2_hidden(D_120, k3_relat_1(k1_wellord2(A_45))) | ~r2_hidden(B_122, A_45) | ~v2_wellord1(k1_wellord2(A_45)) | ~r2_hidden(D_120, k1_wellord1(k1_wellord2(A_45), B_122)) | ~v1_relat_1(k1_wellord2(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_383])).
% 7.82/2.57  tff(c_417, plain, (![D_123, A_124, B_125]: (r2_hidden(D_123, A_124) | ~r2_hidden(B_125, A_124) | ~v2_wellord1(k1_wellord2(A_124)) | ~r2_hidden(D_123, k1_wellord1(k1_wellord2(A_124), B_125)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_92, c_406])).
% 7.82/2.57  tff(c_440, plain, (![D_123, B_56, A_54]: (r2_hidden(D_123, B_56) | ~r2_hidden(A_54, B_56) | ~v2_wellord1(k1_wellord2(B_56)) | ~r2_hidden(D_123, A_54) | ~r2_hidden(A_54, B_56) | ~v3_ordinal1(B_56) | ~v3_ordinal1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_74, c_417])).
% 7.82/2.57  tff(c_2287, plain, (![D_123]: (r2_hidden(D_123, '#skF_10') | ~v2_wellord1(k1_wellord2('#skF_10')) | ~r2_hidden(D_123, '#skF_9') | ~r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1('#skF_9'))), inference(resolution, [status(thm)], [c_2273, c_440])).
% 7.82/2.57  tff(c_2304, plain, (![D_123]: (r2_hidden(D_123, '#skF_10') | ~v2_wellord1(k1_wellord2('#skF_10')) | ~r2_hidden(D_123, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_2273, c_2287])).
% 7.82/2.57  tff(c_2309, plain, (~v2_wellord1(k1_wellord2('#skF_10'))), inference(splitLeft, [status(thm)], [c_2304])).
% 7.82/2.57  tff(c_2312, plain, (~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_2309])).
% 7.82/2.57  tff(c_2316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_2312])).
% 7.82/2.57  tff(c_2317, plain, (![D_123]: (r2_hidden(D_123, '#skF_10') | ~r2_hidden(D_123, '#skF_9'))), inference(splitRight, [status(thm)], [c_2304])).
% 7.82/2.57  tff(c_70, plain, (![C_51, D_52, A_45]: (r1_tarski(C_51, D_52) | ~r2_hidden(k4_tarski(C_51, D_52), k1_wellord2(A_45)) | ~r2_hidden(D_52, A_45) | ~r2_hidden(C_51, A_45) | ~v1_relat_1(k1_wellord2(A_45)))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.82/2.57  tff(c_281, plain, (![C_100, D_101, A_102]: (r1_tarski(C_100, D_101) | ~r2_hidden(k4_tarski(C_100, D_101), k1_wellord2(A_102)) | ~r2_hidden(D_101, A_102) | ~r2_hidden(C_100, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70])).
% 7.82/2.57  tff(c_288, plain, (![D_17, B_13, A_102]: (r1_tarski(D_17, B_13) | ~r2_hidden(B_13, A_102) | ~r2_hidden(D_17, A_102) | ~r2_hidden(D_17, k1_wellord1(k1_wellord2(A_102), B_13)) | ~v1_relat_1(k1_wellord2(A_102)))), inference(resolution, [status(thm)], [c_12, c_281])).
% 7.82/2.57  tff(c_301, plain, (![D_103, B_104, A_105]: (r1_tarski(D_103, B_104) | ~r2_hidden(B_104, A_105) | ~r2_hidden(D_103, A_105) | ~r2_hidden(D_103, k1_wellord1(k1_wellord2(A_105), B_104)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_288])).
% 7.82/2.57  tff(c_320, plain, (![D_103, A_54, B_56]: (r1_tarski(D_103, A_54) | ~r2_hidden(A_54, B_56) | ~r2_hidden(D_103, B_56) | ~r2_hidden(D_103, A_54) | ~r2_hidden(A_54, B_56) | ~v3_ordinal1(B_56) | ~v3_ordinal1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_74, c_301])).
% 7.82/2.57  tff(c_2289, plain, (![D_103]: (r1_tarski(D_103, '#skF_9') | ~r2_hidden(D_103, '#skF_10') | ~r2_hidden(D_103, '#skF_9') | ~r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1('#skF_9'))), inference(resolution, [status(thm)], [c_2273, c_320])).
% 7.82/2.57  tff(c_2467, plain, (![D_213]: (r1_tarski(D_213, '#skF_9') | ~r2_hidden(D_213, '#skF_10') | ~r2_hidden(D_213, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_2273, c_2289])).
% 7.82/2.57  tff(c_2698, plain, (![D_215]: (r1_tarski(D_215, '#skF_9') | ~r2_hidden(D_215, '#skF_9'))), inference(resolution, [status(thm)], [c_2317, c_2467])).
% 7.82/2.57  tff(c_2779, plain, (![B_90]: (r1_tarski('#skF_6'(k1_wellord2('#skF_9'), B_90), '#skF_9') | r1_tarski('#skF_9', B_90) | ~v2_wellord1(k1_wellord2('#skF_9')))), inference(resolution, [status(thm)], [c_243, c_2698])).
% 7.82/2.57  tff(c_3221, plain, (~v2_wellord1(k1_wellord2('#skF_9'))), inference(splitLeft, [status(thm)], [c_2779])).
% 7.82/2.57  tff(c_3224, plain, (~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_3221])).
% 7.82/2.57  tff(c_3228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_3224])).
% 7.82/2.57  tff(c_3230, plain, (v2_wellord1(k1_wellord2('#skF_9'))), inference(splitRight, [status(thm)], [c_2779])).
% 7.82/2.57  tff(c_2382, plain, (![D_212]: (r2_hidden(D_212, '#skF_10') | ~r2_hidden(D_212, '#skF_9'))), inference(splitRight, [status(thm)], [c_2304])).
% 7.82/2.57  tff(c_44, plain, (![A_33, B_37]: (~r2_hidden('#skF_6'(A_33, B_37), B_37) | r1_tarski(k3_relat_1(A_33), B_37) | ~v2_wellord1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.82/2.57  tff(c_3316, plain, (![A_224]: (r1_tarski(k3_relat_1(A_224), '#skF_10') | ~v2_wellord1(A_224) | ~v1_relat_1(A_224) | ~r2_hidden('#skF_6'(A_224, '#skF_10'), '#skF_9'))), inference(resolution, [status(thm)], [c_2382, c_44])).
% 7.82/2.57  tff(c_3329, plain, (r1_tarski(k3_relat_1(k1_wellord2('#skF_9')), '#skF_10') | ~v1_relat_1(k1_wellord2('#skF_9')) | r1_tarski('#skF_9', '#skF_10') | ~v2_wellord1(k1_wellord2('#skF_9'))), inference(resolution, [status(thm)], [c_243, c_3316])).
% 7.82/2.57  tff(c_3347, plain, (r1_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3230, c_72, c_92, c_3329])).
% 7.82/2.57  tff(c_3349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_547, c_3347])).
% 7.82/2.57  tff(c_3350, plain, (~r1_tarski(k1_wellord1(k1_wellord2('#skF_9'), '#skF_10'), '#skF_9') | ~v2_wellord1(k1_wellord2('#skF_9'))), inference(splitRight, [status(thm)], [c_2242])).
% 7.82/2.57  tff(c_3382, plain, (~v2_wellord1(k1_wellord2('#skF_9'))), inference(splitLeft, [status(thm)], [c_3350])).
% 7.82/2.57  tff(c_3385, plain, (~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_3382])).
% 7.82/2.57  tff(c_3389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_3385])).
% 7.82/2.57  tff(c_3391, plain, (v2_wellord1(k1_wellord2('#skF_9'))), inference(splitRight, [status(thm)], [c_3350])).
% 7.82/2.57  tff(c_3351, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_2242])).
% 7.82/2.57  tff(c_3361, plain, (![D_123]: (r2_hidden(D_123, '#skF_9') | ~v2_wellord1(k1_wellord2('#skF_9')) | ~r2_hidden(D_123, '#skF_10') | ~r2_hidden('#skF_10', '#skF_9') | ~v3_ordinal1('#skF_9') | ~v3_ordinal1('#skF_10'))), inference(resolution, [status(thm)], [c_3351, c_440])).
% 7.82/2.57  tff(c_3378, plain, (![D_123]: (r2_hidden(D_123, '#skF_9') | ~v2_wellord1(k1_wellord2('#skF_9')) | ~r2_hidden(D_123, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_3351, c_3361])).
% 7.82/2.57  tff(c_3399, plain, (![D_225]: (r2_hidden(D_225, '#skF_9') | ~r2_hidden(D_225, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_3391, c_3378])).
% 7.82/2.57  tff(c_3478, plain, (![B_90]: (r2_hidden('#skF_6'(k1_wellord2('#skF_10'), B_90), '#skF_9') | r1_tarski('#skF_10', B_90) | ~v2_wellord1(k1_wellord2('#skF_10')))), inference(resolution, [status(thm)], [c_243, c_3399])).
% 7.82/2.57  tff(c_3901, plain, (~v2_wellord1(k1_wellord2('#skF_10'))), inference(splitLeft, [status(thm)], [c_3478])).
% 7.82/2.57  tff(c_3904, plain, (~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_3901])).
% 7.82/2.57  tff(c_3908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_3904])).
% 7.82/2.57  tff(c_3910, plain, (v2_wellord1(k1_wellord2('#skF_10'))), inference(splitRight, [status(thm)], [c_3478])).
% 7.82/2.57  tff(c_3988, plain, (![B_231]: (r2_hidden('#skF_6'(k1_wellord2('#skF_10'), B_231), '#skF_9') | r1_tarski('#skF_10', B_231))), inference(splitRight, [status(thm)], [c_3478])).
% 7.82/2.57  tff(c_4004, plain, (r1_tarski(k3_relat_1(k1_wellord2('#skF_10')), '#skF_9') | ~v2_wellord1(k1_wellord2('#skF_10')) | ~v1_relat_1(k1_wellord2('#skF_10')) | r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_3988, c_44])).
% 7.82/2.57  tff(c_4025, plain, (r1_tarski('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3910, c_92, c_4004])).
% 7.82/2.57  tff(c_4027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_548, c_4025])).
% 7.82/2.57  tff(c_4028, plain, (~r2_hidden('#skF_10', '#skF_9') | ~v2_wellord1(k1_wellord2('#skF_9'))), inference(splitRight, [status(thm)], [c_546])).
% 7.82/2.57  tff(c_4034, plain, (~v2_wellord1(k1_wellord2('#skF_9'))), inference(splitLeft, [status(thm)], [c_4028])).
% 7.82/2.57  tff(c_4037, plain, (~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_76, c_4034])).
% 7.82/2.57  tff(c_4041, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_4037])).
% 7.82/2.57  tff(c_4043, plain, (v2_wellord1(k1_wellord2('#skF_9'))), inference(splitRight, [status(thm)], [c_4028])).
% 7.82/2.57  tff(c_4042, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_4028])).
% 7.82/2.57  tff(c_4046, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_8, c_4042])).
% 7.82/2.57  tff(c_4052, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_4046])).
% 7.82/2.57  tff(c_4053, plain, (r2_hidden('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_80, c_4052])).
% 7.82/2.57  tff(c_4119, plain, (![D_234, A_235, B_236]: (r1_tarski(D_234, A_235) | ~r2_hidden(A_235, B_236) | ~r2_hidden(D_234, B_236) | ~r2_hidden(D_234, A_235) | ~r2_hidden(A_235, B_236) | ~v3_ordinal1(B_236) | ~v3_ordinal1(A_235))), inference(superposition, [status(thm), theory('equality')], [c_74, c_301])).
% 7.82/2.57  tff(c_4123, plain, (![D_234]: (r1_tarski(D_234, '#skF_9') | ~r2_hidden(D_234, '#skF_10') | ~r2_hidden(D_234, '#skF_9') | ~r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1('#skF_9'))), inference(resolution, [status(thm)], [c_4053, c_4119])).
% 7.82/2.57  tff(c_4164, plain, (![D_237]: (r1_tarski(D_237, '#skF_9') | ~r2_hidden(D_237, '#skF_10') | ~r2_hidden(D_237, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_4053, c_4123])).
% 7.82/2.57  tff(c_4203, plain, (![B_90]: (r1_tarski('#skF_6'(k1_wellord2('#skF_10'), B_90), '#skF_9') | ~r2_hidden('#skF_6'(k1_wellord2('#skF_10'), B_90), '#skF_9') | r1_tarski('#skF_10', B_90) | ~v2_wellord1(k1_wellord2('#skF_10')))), inference(resolution, [status(thm)], [c_243, c_4164])).
% 7.82/2.57  tff(c_4310, plain, (~v2_wellord1(k1_wellord2('#skF_10'))), inference(splitLeft, [status(thm)], [c_4203])).
% 7.82/2.57  tff(c_4326, plain, (~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_4310])).
% 7.82/2.57  tff(c_4330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_4326])).
% 7.82/2.57  tff(c_4332, plain, (v2_wellord1(k1_wellord2('#skF_10'))), inference(splitRight, [status(thm)], [c_4203])).
% 7.82/2.57  tff(c_4418, plain, (![D_248, B_249, A_250]: (r2_hidden(D_248, B_249) | ~r2_hidden(A_250, B_249) | ~v2_wellord1(k1_wellord2(B_249)) | ~r2_hidden(D_248, A_250) | ~r2_hidden(A_250, B_249) | ~v3_ordinal1(B_249) | ~v3_ordinal1(A_250))), inference(superposition, [status(thm), theory('equality')], [c_74, c_417])).
% 7.82/2.57  tff(c_4424, plain, (![D_248]: (r2_hidden(D_248, '#skF_10') | ~v2_wellord1(k1_wellord2('#skF_10')) | ~r2_hidden(D_248, '#skF_9') | ~r2_hidden('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1('#skF_9'))), inference(resolution, [status(thm)], [c_4053, c_4418])).
% 7.82/2.57  tff(c_4468, plain, (![D_251]: (r2_hidden(D_251, '#skF_10') | ~r2_hidden(D_251, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_4053, c_4332, c_4424])).
% 7.82/2.57  tff(c_4639, plain, (![A_257]: (r1_tarski(k3_relat_1(A_257), '#skF_10') | ~v2_wellord1(A_257) | ~v1_relat_1(A_257) | ~r2_hidden('#skF_6'(A_257, '#skF_10'), '#skF_9'))), inference(resolution, [status(thm)], [c_4468, c_44])).
% 7.82/2.57  tff(c_4643, plain, (r1_tarski(k3_relat_1(k1_wellord2('#skF_9')), '#skF_10') | ~v1_relat_1(k1_wellord2('#skF_9')) | r1_tarski('#skF_9', '#skF_10') | ~v2_wellord1(k1_wellord2('#skF_9'))), inference(resolution, [status(thm)], [c_243, c_4639])).
% 7.82/2.57  tff(c_4652, plain, (r1_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4043, c_72, c_92, c_4643])).
% 7.82/2.57  tff(c_4654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_547, c_4652])).
% 7.82/2.57  tff(c_4656, plain, (r1_tarski('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_543])).
% 7.82/2.57  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.82/2.57  tff(c_4658, plain, ('#skF_10'='#skF_9' | ~r1_tarski('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_4656, c_2])).
% 7.82/2.57  tff(c_4661, plain, (~r1_tarski('#skF_10', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_80, c_4658])).
% 7.82/2.57  tff(c_4655, plain, (~r2_hidden('#skF_9', '#skF_10') | ~v2_wellord1(k1_wellord2('#skF_10'))), inference(splitRight, [status(thm)], [c_543])).
% 7.82/2.57  tff(c_4662, plain, (~v2_wellord1(k1_wellord2('#skF_10'))), inference(splitLeft, [status(thm)], [c_4655])).
% 7.82/2.57  tff(c_4665, plain, (~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_4662])).
% 7.82/2.57  tff(c_4669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_4665])).
% 7.82/2.57  tff(c_4671, plain, (v2_wellord1(k1_wellord2('#skF_10'))), inference(splitRight, [status(thm)], [c_4655])).
% 7.82/2.57  tff(c_4862, plain, (![D_268, B_269, A_270]: (r2_hidden(D_268, B_269) | ~r2_hidden(A_270, B_269) | ~v2_wellord1(k1_wellord2(B_269)) | ~r2_hidden(D_268, A_270) | ~r2_hidden(A_270, B_269) | ~v3_ordinal1(B_269) | ~v3_ordinal1(A_270))), inference(superposition, [status(thm), theory('equality')], [c_74, c_417])).
% 7.82/2.57  tff(c_5254, plain, (![D_291, A_292, B_293]: (r2_hidden(D_291, A_292) | ~v2_wellord1(k1_wellord2(A_292)) | ~r2_hidden(D_291, B_293) | ~r2_hidden(B_293, A_292) | B_293=A_292 | r2_hidden(A_292, B_293) | ~v3_ordinal1(B_293) | ~v3_ordinal1(A_292))), inference(resolution, [status(thm)], [c_8, c_4862])).
% 7.82/2.57  tff(c_5256, plain, (![D_291, B_293]: (r2_hidden(D_291, '#skF_10') | ~r2_hidden(D_291, B_293) | ~r2_hidden(B_293, '#skF_10') | B_293='#skF_10' | r2_hidden('#skF_10', B_293) | ~v3_ordinal1(B_293) | ~v3_ordinal1('#skF_10'))), inference(resolution, [status(thm)], [c_4671, c_5254])).
% 7.82/2.57  tff(c_5263, plain, (![D_294, B_295]: (r2_hidden(D_294, '#skF_10') | ~r2_hidden(D_294, B_295) | ~r2_hidden(B_295, '#skF_10') | B_295='#skF_10' | r2_hidden('#skF_10', B_295) | ~v3_ordinal1(B_295))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5256])).
% 7.82/2.57  tff(c_5395, plain, (![B_302, A_303]: (r2_hidden(B_302, '#skF_10') | ~r2_hidden(A_303, '#skF_10') | A_303='#skF_10' | r2_hidden('#skF_10', A_303) | B_302=A_303 | r2_hidden(A_303, B_302) | ~v3_ordinal1(B_302) | ~v3_ordinal1(A_303))), inference(resolution, [status(thm)], [c_8, c_5263])).
% 7.82/2.57  tff(c_5419, plain, (![B_302, B_5]: (r2_hidden(B_302, '#skF_10') | B_5=B_302 | r2_hidden(B_5, B_302) | ~v3_ordinal1(B_302) | B_5='#skF_10' | r2_hidden('#skF_10', B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1('#skF_10'))), inference(resolution, [status(thm)], [c_8, c_5395])).
% 7.82/2.57  tff(c_5497, plain, (![B_304, B_305]: (r2_hidden(B_304, '#skF_10') | B_305=B_304 | r2_hidden(B_305, B_304) | ~v3_ordinal1(B_304) | B_305='#skF_10' | r2_hidden('#skF_10', B_305) | ~v3_ordinal1(B_305))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5419])).
% 7.82/2.57  tff(c_136, plain, (![B_73, A_74]: (k1_wellord1(k1_wellord2(B_73), A_74)=A_74 | ~r2_hidden(A_74, B_73) | ~v3_ordinal1(B_73) | ~v3_ordinal1(A_74))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.82/2.57  tff(c_14, plain, (![D_17, A_6]: (~r2_hidden(D_17, k1_wellord1(A_6, D_17)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.82/2.57  tff(c_142, plain, (![A_74, B_73]: (~r2_hidden(A_74, A_74) | ~v1_relat_1(k1_wellord2(B_73)) | ~r2_hidden(A_74, B_73) | ~v3_ordinal1(B_73) | ~v3_ordinal1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_136, c_14])).
% 7.82/2.57  tff(c_148, plain, (![A_74, B_73]: (~r2_hidden(A_74, A_74) | ~r2_hidden(A_74, B_73) | ~v3_ordinal1(B_73) | ~v3_ordinal1(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_142])).
% 7.82/2.57  tff(c_5539, plain, (![B_73, B_305]: (~r2_hidden('#skF_10', B_73) | ~v3_ordinal1(B_73) | r2_hidden(B_305, '#skF_10') | ~v3_ordinal1('#skF_10') | B_305='#skF_10' | r2_hidden('#skF_10', B_305) | ~v3_ordinal1(B_305))), inference(resolution, [status(thm)], [c_5497, c_148])).
% 7.82/2.57  tff(c_5673, plain, (![B_73, B_305]: (~r2_hidden('#skF_10', B_73) | ~v3_ordinal1(B_73) | r2_hidden(B_305, '#skF_10') | B_305='#skF_10' | r2_hidden('#skF_10', B_305) | ~v3_ordinal1(B_305))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5539])).
% 7.82/2.57  tff(c_5715, plain, (![B_306]: (~r2_hidden('#skF_10', B_306) | ~v3_ordinal1(B_306))), inference(splitLeft, [status(thm)], [c_5673])).
% 7.82/2.57  tff(c_5734, plain, (![A_3]: (A_3='#skF_10' | r2_hidden(A_3, '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1(A_3))), inference(resolution, [status(thm)], [c_8, c_5715])).
% 7.82/2.57  tff(c_5754, plain, (![A_307]: (A_307='#skF_10' | r2_hidden(A_307, '#skF_10') | ~v3_ordinal1(A_307))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5734])).
% 7.82/2.57  tff(c_4670, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_4655])).
% 7.82/2.57  tff(c_5783, plain, ('#skF_10'='#skF_9' | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_5754, c_4670])).
% 7.82/2.57  tff(c_5830, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_5783])).
% 7.82/2.57  tff(c_5832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_5830])).
% 7.82/2.57  tff(c_5833, plain, (![B_305]: (r2_hidden(B_305, '#skF_10') | B_305='#skF_10' | r2_hidden('#skF_10', B_305) | ~v3_ordinal1(B_305))), inference(splitRight, [status(thm)], [c_5673])).
% 7.82/2.57  tff(c_5854, plain, (![B_308]: (r2_hidden(B_308, '#skF_10') | B_308='#skF_10' | r2_hidden('#skF_10', B_308) | ~v3_ordinal1(B_308))), inference(splitRight, [status(thm)], [c_5673])).
% 7.82/2.57  tff(c_5908, plain, (![D_123, B_308]: (r2_hidden(D_123, B_308) | ~v2_wellord1(k1_wellord2(B_308)) | ~r2_hidden(D_123, '#skF_10') | ~r2_hidden('#skF_10', B_308) | ~v3_ordinal1('#skF_10') | r2_hidden(B_308, '#skF_10') | B_308='#skF_10' | ~v3_ordinal1(B_308))), inference(resolution, [status(thm)], [c_5854, c_440])).
% 7.82/2.57  tff(c_6046, plain, (![D_314, B_315]: (r2_hidden(D_314, B_315) | ~v2_wellord1(k1_wellord2(B_315)) | ~r2_hidden(D_314, '#skF_10') | ~r2_hidden('#skF_10', B_315) | r2_hidden(B_315, '#skF_10') | B_315='#skF_10' | ~v3_ordinal1(B_315))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5908])).
% 7.82/2.57  tff(c_6056, plain, (![D_316, A_317]: (r2_hidden(D_316, A_317) | ~r2_hidden(D_316, '#skF_10') | ~r2_hidden('#skF_10', A_317) | r2_hidden(A_317, '#skF_10') | A_317='#skF_10' | ~v3_ordinal1(A_317))), inference(resolution, [status(thm)], [c_76, c_6046])).
% 7.82/2.57  tff(c_6085, plain, (![B_90, A_317]: (r2_hidden('#skF_6'(k1_wellord2('#skF_10'), B_90), A_317) | ~r2_hidden('#skF_10', A_317) | r2_hidden(A_317, '#skF_10') | A_317='#skF_10' | ~v3_ordinal1(A_317) | r1_tarski('#skF_10', B_90) | ~v2_wellord1(k1_wellord2('#skF_10')))), inference(resolution, [status(thm)], [c_243, c_6056])).
% 7.82/2.57  tff(c_6192, plain, (![B_320, A_321]: (r2_hidden('#skF_6'(k1_wellord2('#skF_10'), B_320), A_321) | ~r2_hidden('#skF_10', A_321) | r2_hidden(A_321, '#skF_10') | A_321='#skF_10' | ~v3_ordinal1(A_321) | r1_tarski('#skF_10', B_320))), inference(demodulation, [status(thm), theory('equality')], [c_4671, c_6085])).
% 7.82/2.57  tff(c_6243, plain, (![A_321]: (r1_tarski(k3_relat_1(k1_wellord2('#skF_10')), A_321) | ~v2_wellord1(k1_wellord2('#skF_10')) | ~v1_relat_1(k1_wellord2('#skF_10')) | ~r2_hidden('#skF_10', A_321) | r2_hidden(A_321, '#skF_10') | A_321='#skF_10' | ~v3_ordinal1(A_321) | r1_tarski('#skF_10', A_321))), inference(resolution, [status(thm)], [c_6192, c_44])).
% 7.82/2.57  tff(c_6277, plain, (![A_322]: (~r2_hidden('#skF_10', A_322) | r2_hidden(A_322, '#skF_10') | A_322='#skF_10' | ~v3_ordinal1(A_322) | r1_tarski('#skF_10', A_322))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4671, c_92, c_6243])).
% 7.82/2.57  tff(c_6314, plain, (![B_323]: (r1_tarski('#skF_10', B_323) | r2_hidden(B_323, '#skF_10') | B_323='#skF_10' | ~v3_ordinal1(B_323))), inference(resolution, [status(thm)], [c_5833, c_6277])).
% 7.82/2.57  tff(c_6348, plain, (r1_tarski('#skF_10', '#skF_9') | '#skF_10'='#skF_9' | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_6314, c_4670])).
% 7.82/2.57  tff(c_6398, plain, (r1_tarski('#skF_10', '#skF_9') | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6348])).
% 7.82/2.57  tff(c_6400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_4661, c_6398])).
% 7.82/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/2.57  
% 7.82/2.57  Inference rules
% 7.82/2.57  ----------------------
% 7.82/2.57  #Ref     : 0
% 7.82/2.57  #Sup     : 1316
% 7.82/2.57  #Fact    : 16
% 7.82/2.57  #Define  : 0
% 7.82/2.57  #Split   : 15
% 7.82/2.57  #Chain   : 0
% 7.82/2.57  #Close   : 0
% 7.82/2.57  
% 7.82/2.57  Ordering : KBO
% 7.82/2.57  
% 7.82/2.57  Simplification rules
% 7.82/2.57  ----------------------
% 7.82/2.57  #Subsume      : 70
% 7.82/2.57  #Demod        : 587
% 7.82/2.57  #Tautology    : 108
% 7.82/2.57  #SimpNegUnit  : 21
% 7.82/2.57  #BackRed      : 0
% 7.82/2.57  
% 7.82/2.57  #Partial instantiations: 0
% 7.82/2.57  #Strategies tried      : 1
% 7.82/2.57  
% 7.82/2.57  Timing (in seconds)
% 7.82/2.57  ----------------------
% 7.82/2.57  Preprocessing        : 0.36
% 7.82/2.57  Parsing              : 0.18
% 7.82/2.57  CNF conversion       : 0.03
% 7.82/2.57  Main loop            : 1.48
% 7.82/2.57  Inferencing          : 0.41
% 7.82/2.57  Reduction            : 0.38
% 7.82/2.57  Demodulation         : 0.27
% 7.82/2.57  BG Simplification    : 0.08
% 7.82/2.57  Subsumption          : 0.49
% 7.82/2.57  Abstraction          : 0.09
% 7.82/2.57  MUC search           : 0.00
% 7.82/2.57  Cooper               : 0.00
% 7.82/2.57  Total                : 1.90
% 7.82/2.58  Index Insertion      : 0.00
% 7.82/2.58  Index Deletion       : 0.00
% 7.82/2.58  Index Matching       : 0.00
% 7.82/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
