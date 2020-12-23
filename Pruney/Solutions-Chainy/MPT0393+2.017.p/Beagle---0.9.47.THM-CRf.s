%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:19 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 618 expanded)
%              Number of leaves         :   27 ( 215 expanded)
%              Depth                    :   26
%              Number of atoms          :  158 (1425 expanded)
%              Number of equality atoms :   59 ( 399 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_147,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden(A_65,B_66)
      | ~ r2_hidden(A_65,k4_xboole_0(B_66,k1_tarski(C_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2972,plain,(
    ! [B_3169,C_3170,B_3171] :
      ( r2_hidden('#skF_1'(k4_xboole_0(B_3169,k1_tarski(C_3170)),B_3171),B_3169)
      | r1_tarski(k4_xboole_0(B_3169,k1_tarski(C_3170)),B_3171) ) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3012,plain,(
    ! [B_3172,C_3173] : r1_tarski(k4_xboole_0(B_3172,k1_tarski(C_3173)),B_3172) ),
    inference(resolution,[status(thm)],[c_2972,c_4])).

tff(c_36,plain,(
    ! [B_20] : r1_tarski(k1_xboole_0,k1_tarski(B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_153,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_325,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_94)
      | ~ r1_tarski(A_92,B_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_371,plain,(
    ! [A_96,A_97,B_98] :
      ( A_96 = '#skF_1'(A_97,B_98)
      | ~ r1_tarski(A_97,k1_tarski(A_96))
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_325,c_14])).

tff(c_385,plain,(
    ! [B_99,B_100] :
      ( B_99 = '#skF_1'(k1_xboole_0,B_100)
      | r1_tarski(k1_xboole_0,B_100) ) ),
    inference(resolution,[status(thm)],[c_36,c_371])).

tff(c_113,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,B_57),A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_167,plain,(
    ! [A_73,B_74] :
      ( '#skF_1'(k1_tarski(A_73),B_74) = A_73
      | r1_tarski(k1_tarski(A_73),B_74) ) ),
    inference(resolution,[status(thm)],[c_113,c_14])).

tff(c_102,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    ! [B_20] :
      ( k1_tarski(B_20) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(B_20),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_203,plain,(
    ! [A_79] :
      ( k1_tarski(A_79) = k1_xboole_0
      | '#skF_1'(k1_tarski(A_79),k1_xboole_0) = A_79 ) ),
    inference(resolution,[status(thm)],[c_167,c_107])).

tff(c_228,plain,(
    ! [A_80] :
      ( ~ r2_hidden(A_80,k1_xboole_0)
      | r1_tarski(k1_tarski(A_80),k1_xboole_0)
      | k1_tarski(A_80) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_4])).

tff(c_242,plain,(
    ! [A_81] :
      ( ~ r2_hidden(A_81,k1_xboole_0)
      | k1_tarski(A_81) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_228,c_107])).

tff(c_267,plain,(
    ! [B_85] :
      ( k1_tarski('#skF_1'(k1_xboole_0,B_85)) = k1_xboole_0
      | r1_tarski(k1_xboole_0,B_85) ) ),
    inference(resolution,[status(thm)],[c_6,c_242])).

tff(c_40,plain,(
    ! [C_23,B_22] : ~ r2_hidden(C_23,k4_xboole_0(B_22,k1_tarski(C_23))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_299,plain,(
    ! [B_85,B_22] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_85),k4_xboole_0(B_22,k1_xboole_0))
      | r1_tarski(k1_xboole_0,B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_40])).

tff(c_361,plain,(
    ! [B_22,B_93] :
      ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(B_22,k1_xboole_0))
      | r1_tarski(k1_xboole_0,B_93) ) ),
    inference(resolution,[status(thm)],[c_325,c_299])).

tff(c_369,plain,(
    ! [B_22] : ~ r1_tarski(k1_xboole_0,k4_xboole_0(B_22,k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_906,plain,(
    ! [B_1069] : '#skF_1'(k1_xboole_0,k4_xboole_0(B_1069,k1_xboole_0)) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_385,c_369])).

tff(c_880,plain,(
    ! [B_99,B_22] : B_99 = '#skF_1'(k1_xboole_0,k4_xboole_0(B_22,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_385,c_369])).

tff(c_1616,plain,(
    ! [B_2050] : B_2050 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_880])).

tff(c_66,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1723,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1616,c_66])).

tff(c_1729,plain,(
    ! [B_3087] : r1_tarski(k1_xboole_0,B_3087) ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1738,plain,(
    ! [B_3087] :
      ( k1_xboole_0 = B_3087
      | ~ r1_tarski(B_3087,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1729,c_8])).

tff(c_3047,plain,(
    ! [C_3174] : k4_xboole_0(k1_xboole_0,k1_tarski(C_3174)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3012,c_1738])).

tff(c_3075,plain,(
    ! [C_3174] : ~ r2_hidden(C_3174,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3047,c_40])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( k1_tarski(B_20) = A_19
      | k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_tarski(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3045,plain,(
    ! [B_20,C_3173] :
      ( k4_xboole_0(k1_tarski(B_20),k1_tarski(C_3173)) = k1_tarski(B_20)
      | k4_xboole_0(k1_tarski(B_20),k1_tarski(C_3173)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3012,c_32])).

tff(c_3265,plain,(
    ! [B_3183,C_3184] :
      ( k4_xboole_0(k1_tarski(B_3183),k1_tarski(C_3184)) = k1_xboole_0
      | k1_tarski(B_3183) != k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3045])).

tff(c_38,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(A_21,k4_xboole_0(B_22,k1_tarski(C_23)))
      | C_23 = A_21
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3294,plain,(
    ! [A_21,C_3184,B_3183] :
      ( r2_hidden(A_21,k1_xboole_0)
      | C_3184 = A_21
      | ~ r2_hidden(A_21,k1_tarski(B_3183))
      | k1_tarski(B_3183) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3265,c_38])).

tff(c_3314,plain,(
    ! [C_3185,A_3186,B_3187] :
      ( C_3185 = A_3186
      | ~ r2_hidden(A_3186,k1_tarski(B_3187))
      | k1_tarski(B_3187) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3075,c_3294])).

tff(c_3550,plain,(
    ! [C_3200,B_3201,B_3202] :
      ( C_3200 = '#skF_1'(k1_tarski(B_3201),B_3202)
      | k1_tarski(B_3201) != k1_xboole_0
      | r1_tarski(k1_tarski(B_3201),B_3202) ) ),
    inference(resolution,[status(thm)],[c_6,c_3314])).

tff(c_16,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_159,plain,(
    ! [C_12,B_69] :
      ( r2_hidden(C_12,B_69)
      | ~ r1_tarski(k1_tarski(C_12),B_69) ) ),
    inference(resolution,[status(thm)],[c_16,c_153])).

tff(c_4476,plain,(
    ! [B_5023,B_5024,C_5025] :
      ( r2_hidden(B_5023,B_5024)
      | C_5025 = '#skF_1'(k1_tarski(B_5023),B_5024)
      | k1_tarski(B_5023) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3550,c_159])).

tff(c_5382,plain,(
    ! [C_12,B_5023,B_5024] :
      ( r2_hidden(C_12,'#skF_1'(k1_tarski(B_5023),B_5024))
      | r2_hidden(B_5023,B_5024)
      | k1_tarski(B_5023) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4476,c_16])).

tff(c_6265,plain,(
    ! [C_8003,B_8004,B_8005] :
      ( ~ r2_hidden(C_8003,'#skF_1'(k1_tarski(B_8004),B_8005))
      | r2_hidden(B_8004,B_8005)
      | k1_tarski(B_8004) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4476,c_40])).

tff(c_6373,plain,(
    ! [B_8062,B_8063] :
      ( r2_hidden(B_8062,B_8063)
      | k1_tarski(B_8062) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5382,c_6265])).

tff(c_6449,plain,(
    ! [B_8062] : k1_tarski(B_8062) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6373,c_40])).

tff(c_2124,plain,(
    ! [A_3116,C_3117] :
      ( r2_hidden('#skF_4'(A_3116,k1_setfam_1(A_3116),C_3117),A_3116)
      | r2_hidden(C_3117,k1_setfam_1(A_3116))
      | k1_xboole_0 = A_3116 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2155,plain,(
    ! [A_8,C_3117] :
      ( '#skF_4'(k1_tarski(A_8),k1_setfam_1(k1_tarski(A_8)),C_3117) = A_8
      | r2_hidden(C_3117,k1_setfam_1(k1_tarski(A_8)))
      | k1_tarski(A_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2124,c_14])).

tff(c_6526,plain,(
    ! [A_8095,C_8096] :
      ( '#skF_4'(k1_tarski(A_8095),k1_setfam_1(k1_tarski(A_8095)),C_8096) = A_8095
      | r2_hidden(C_8096,k1_setfam_1(k1_tarski(A_8095))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6449,c_2155])).

tff(c_58,plain,(
    ! [C_36,A_24] :
      ( ~ r2_hidden(C_36,'#skF_4'(A_24,k1_setfam_1(A_24),C_36))
      | r2_hidden(C_36,k1_setfam_1(A_24))
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6535,plain,(
    ! [C_8096,A_8095] :
      ( ~ r2_hidden(C_8096,A_8095)
      | r2_hidden(C_8096,k1_setfam_1(k1_tarski(A_8095)))
      | k1_tarski(A_8095) = k1_xboole_0
      | r2_hidden(C_8096,k1_setfam_1(k1_tarski(A_8095))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6526,c_58])).

tff(c_6544,plain,(
    ! [C_8096,A_8095] :
      ( ~ r2_hidden(C_8096,A_8095)
      | r2_hidden(C_8096,k1_setfam_1(k1_tarski(A_8095)))
      | r2_hidden(C_8096,k1_setfam_1(k1_tarski(A_8095))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6449,c_6535])).

tff(c_6917,plain,(
    ! [C_8119,A_8120] :
      ( ~ r2_hidden(C_8119,A_8120)
      | r2_hidden(C_8119,k1_setfam_1(k1_tarski(A_8120))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6544])).

tff(c_6980,plain,(
    ! [A_8124,A_8125] :
      ( r1_tarski(A_8124,k1_setfam_1(k1_tarski(A_8125)))
      | ~ r2_hidden('#skF_1'(A_8124,k1_setfam_1(k1_tarski(A_8125))),A_8125) ) ),
    inference(resolution,[status(thm)],[c_6917,c_4])).

tff(c_7027,plain,(
    ! [A_1] : r1_tarski(A_1,k1_setfam_1(k1_tarski(A_1))) ),
    inference(resolution,[status(thm)],[c_6,c_6980])).

tff(c_1861,plain,(
    ! [C_3099,D_3100,A_3101] :
      ( r2_hidden(C_3099,D_3100)
      | ~ r2_hidden(D_3100,A_3101)
      | ~ r2_hidden(C_3099,k1_setfam_1(A_3101))
      | k1_xboole_0 = A_3101 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1876,plain,(
    ! [C_3099,C_12] :
      ( r2_hidden(C_3099,C_12)
      | ~ r2_hidden(C_3099,k1_setfam_1(k1_tarski(C_12)))
      | k1_tarski(C_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_1861])).

tff(c_6455,plain,(
    ! [C_8093,C_8094] :
      ( r2_hidden(C_8093,C_8094)
      | ~ r2_hidden(C_8093,k1_setfam_1(k1_tarski(C_8094))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6449,c_1876])).

tff(c_6580,plain,(
    ! [C_8099,B_8100] :
      ( r2_hidden('#skF_1'(k1_setfam_1(k1_tarski(C_8099)),B_8100),C_8099)
      | r1_tarski(k1_setfam_1(k1_tarski(C_8099)),B_8100) ) ),
    inference(resolution,[status(thm)],[c_6,c_6455])).

tff(c_6620,plain,(
    ! [C_8101] : r1_tarski(k1_setfam_1(k1_tarski(C_8101)),C_8101) ),
    inference(resolution,[status(thm)],[c_6580,c_4])).

tff(c_6650,plain,(
    ! [C_8101] :
      ( k1_setfam_1(k1_tarski(C_8101)) = C_8101
      | ~ r1_tarski(C_8101,k1_setfam_1(k1_tarski(C_8101))) ) ),
    inference(resolution,[status(thm)],[c_6620,c_8])).

tff(c_7056,plain,(
    ! [C_8101] : k1_setfam_1(k1_tarski(C_8101)) = C_8101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7027,c_6650])).

tff(c_7102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7056,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.24  
% 5.92/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.25  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5
% 5.92/2.25  
% 5.92/2.25  %Foreground sorts:
% 5.92/2.25  
% 5.92/2.25  
% 5.92/2.25  %Background operators:
% 5.92/2.25  
% 5.92/2.25  
% 5.92/2.25  %Foreground operators:
% 5.92/2.25  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.92/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.92/2.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.92/2.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.92/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.92/2.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.92/2.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.92/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.92/2.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.92/2.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.92/2.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.92/2.25  tff('#skF_8', type, '#skF_8': $i).
% 5.92/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.92/2.25  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.92/2.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.92/2.25  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.92/2.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.92/2.25  
% 5.92/2.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.92/2.27  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 5.92/2.27  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.92/2.27  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.92/2.27  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.92/2.27  tff(f_86, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 5.92/2.27  tff(f_83, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 5.92/2.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.27  tff(c_147, plain, (![A_65, B_66, C_67]: (r2_hidden(A_65, B_66) | ~r2_hidden(A_65, k4_xboole_0(B_66, k1_tarski(C_67))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.27  tff(c_2972, plain, (![B_3169, C_3170, B_3171]: (r2_hidden('#skF_1'(k4_xboole_0(B_3169, k1_tarski(C_3170)), B_3171), B_3169) | r1_tarski(k4_xboole_0(B_3169, k1_tarski(C_3170)), B_3171))), inference(resolution, [status(thm)], [c_6, c_147])).
% 5.92/2.27  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.27  tff(c_3012, plain, (![B_3172, C_3173]: (r1_tarski(k4_xboole_0(B_3172, k1_tarski(C_3173)), B_3172))), inference(resolution, [status(thm)], [c_2972, c_4])).
% 5.92/2.27  tff(c_36, plain, (![B_20]: (r1_tarski(k1_xboole_0, k1_tarski(B_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.92/2.27  tff(c_153, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.27  tff(c_325, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(A_92, B_93), B_94) | ~r1_tarski(A_92, B_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_6, c_153])).
% 5.92/2.27  tff(c_14, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.27  tff(c_371, plain, (![A_96, A_97, B_98]: (A_96='#skF_1'(A_97, B_98) | ~r1_tarski(A_97, k1_tarski(A_96)) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_325, c_14])).
% 5.92/2.27  tff(c_385, plain, (![B_99, B_100]: (B_99='#skF_1'(k1_xboole_0, B_100) | r1_tarski(k1_xboole_0, B_100))), inference(resolution, [status(thm)], [c_36, c_371])).
% 5.92/2.27  tff(c_113, plain, (![A_56, B_57]: (r2_hidden('#skF_1'(A_56, B_57), A_56) | r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.92/2.27  tff(c_167, plain, (![A_73, B_74]: ('#skF_1'(k1_tarski(A_73), B_74)=A_73 | r1_tarski(k1_tarski(A_73), B_74))), inference(resolution, [status(thm)], [c_113, c_14])).
% 5.92/2.27  tff(c_102, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.92/2.27  tff(c_107, plain, (![B_20]: (k1_tarski(B_20)=k1_xboole_0 | ~r1_tarski(k1_tarski(B_20), k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_102])).
% 5.92/2.27  tff(c_203, plain, (![A_79]: (k1_tarski(A_79)=k1_xboole_0 | '#skF_1'(k1_tarski(A_79), k1_xboole_0)=A_79)), inference(resolution, [status(thm)], [c_167, c_107])).
% 5.92/2.27  tff(c_228, plain, (![A_80]: (~r2_hidden(A_80, k1_xboole_0) | r1_tarski(k1_tarski(A_80), k1_xboole_0) | k1_tarski(A_80)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_203, c_4])).
% 5.92/2.27  tff(c_242, plain, (![A_81]: (~r2_hidden(A_81, k1_xboole_0) | k1_tarski(A_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_228, c_107])).
% 5.92/2.27  tff(c_267, plain, (![B_85]: (k1_tarski('#skF_1'(k1_xboole_0, B_85))=k1_xboole_0 | r1_tarski(k1_xboole_0, B_85))), inference(resolution, [status(thm)], [c_6, c_242])).
% 5.92/2.27  tff(c_40, plain, (![C_23, B_22]: (~r2_hidden(C_23, k4_xboole_0(B_22, k1_tarski(C_23))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.27  tff(c_299, plain, (![B_85, B_22]: (~r2_hidden('#skF_1'(k1_xboole_0, B_85), k4_xboole_0(B_22, k1_xboole_0)) | r1_tarski(k1_xboole_0, B_85))), inference(superposition, [status(thm), theory('equality')], [c_267, c_40])).
% 5.92/2.27  tff(c_361, plain, (![B_22, B_93]: (~r1_tarski(k1_xboole_0, k4_xboole_0(B_22, k1_xboole_0)) | r1_tarski(k1_xboole_0, B_93))), inference(resolution, [status(thm)], [c_325, c_299])).
% 5.92/2.27  tff(c_369, plain, (![B_22]: (~r1_tarski(k1_xboole_0, k4_xboole_0(B_22, k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_361])).
% 5.92/2.27  tff(c_906, plain, (![B_1069]: ('#skF_1'(k1_xboole_0, k4_xboole_0(B_1069, k1_xboole_0))='#skF_8')), inference(resolution, [status(thm)], [c_385, c_369])).
% 5.92/2.27  tff(c_880, plain, (![B_99, B_22]: (B_99='#skF_1'(k1_xboole_0, k4_xboole_0(B_22, k1_xboole_0)))), inference(resolution, [status(thm)], [c_385, c_369])).
% 5.92/2.27  tff(c_1616, plain, (![B_2050]: (B_2050='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_906, c_880])).
% 5.92/2.27  tff(c_66, plain, (k1_setfam_1(k1_tarski('#skF_8'))!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.92/2.27  tff(c_1723, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1616, c_66])).
% 5.92/2.27  tff(c_1729, plain, (![B_3087]: (r1_tarski(k1_xboole_0, B_3087))), inference(splitRight, [status(thm)], [c_361])).
% 5.92/2.27  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.92/2.27  tff(c_1738, plain, (![B_3087]: (k1_xboole_0=B_3087 | ~r1_tarski(B_3087, k1_xboole_0))), inference(resolution, [status(thm)], [c_1729, c_8])).
% 5.92/2.27  tff(c_3047, plain, (![C_3174]: (k4_xboole_0(k1_xboole_0, k1_tarski(C_3174))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3012, c_1738])).
% 5.92/2.27  tff(c_3075, plain, (![C_3174]: (~r2_hidden(C_3174, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3047, c_40])).
% 5.92/2.27  tff(c_32, plain, (![B_20, A_19]: (k1_tarski(B_20)=A_19 | k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_tarski(B_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.92/2.27  tff(c_3045, plain, (![B_20, C_3173]: (k4_xboole_0(k1_tarski(B_20), k1_tarski(C_3173))=k1_tarski(B_20) | k4_xboole_0(k1_tarski(B_20), k1_tarski(C_3173))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3012, c_32])).
% 5.92/2.27  tff(c_3265, plain, (![B_3183, C_3184]: (k4_xboole_0(k1_tarski(B_3183), k1_tarski(C_3184))=k1_xboole_0 | k1_tarski(B_3183)!=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_3045])).
% 5.92/2.27  tff(c_38, plain, (![A_21, B_22, C_23]: (r2_hidden(A_21, k4_xboole_0(B_22, k1_tarski(C_23))) | C_23=A_21 | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.92/2.27  tff(c_3294, plain, (![A_21, C_3184, B_3183]: (r2_hidden(A_21, k1_xboole_0) | C_3184=A_21 | ~r2_hidden(A_21, k1_tarski(B_3183)) | k1_tarski(B_3183)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3265, c_38])).
% 5.92/2.27  tff(c_3314, plain, (![C_3185, A_3186, B_3187]: (C_3185=A_3186 | ~r2_hidden(A_3186, k1_tarski(B_3187)) | k1_tarski(B_3187)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3075, c_3294])).
% 5.92/2.27  tff(c_3550, plain, (![C_3200, B_3201, B_3202]: (C_3200='#skF_1'(k1_tarski(B_3201), B_3202) | k1_tarski(B_3201)!=k1_xboole_0 | r1_tarski(k1_tarski(B_3201), B_3202))), inference(resolution, [status(thm)], [c_6, c_3314])).
% 5.92/2.27  tff(c_16, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.27  tff(c_159, plain, (![C_12, B_69]: (r2_hidden(C_12, B_69) | ~r1_tarski(k1_tarski(C_12), B_69))), inference(resolution, [status(thm)], [c_16, c_153])).
% 5.92/2.27  tff(c_4476, plain, (![B_5023, B_5024, C_5025]: (r2_hidden(B_5023, B_5024) | C_5025='#skF_1'(k1_tarski(B_5023), B_5024) | k1_tarski(B_5023)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3550, c_159])).
% 5.92/2.27  tff(c_5382, plain, (![C_12, B_5023, B_5024]: (r2_hidden(C_12, '#skF_1'(k1_tarski(B_5023), B_5024)) | r2_hidden(B_5023, B_5024) | k1_tarski(B_5023)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4476, c_16])).
% 5.92/2.27  tff(c_6265, plain, (![C_8003, B_8004, B_8005]: (~r2_hidden(C_8003, '#skF_1'(k1_tarski(B_8004), B_8005)) | r2_hidden(B_8004, B_8005) | k1_tarski(B_8004)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4476, c_40])).
% 5.92/2.27  tff(c_6373, plain, (![B_8062, B_8063]: (r2_hidden(B_8062, B_8063) | k1_tarski(B_8062)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_5382, c_6265])).
% 5.92/2.27  tff(c_6449, plain, (![B_8062]: (k1_tarski(B_8062)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6373, c_40])).
% 5.92/2.27  tff(c_2124, plain, (![A_3116, C_3117]: (r2_hidden('#skF_4'(A_3116, k1_setfam_1(A_3116), C_3117), A_3116) | r2_hidden(C_3117, k1_setfam_1(A_3116)) | k1_xboole_0=A_3116)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.92/2.27  tff(c_2155, plain, (![A_8, C_3117]: ('#skF_4'(k1_tarski(A_8), k1_setfam_1(k1_tarski(A_8)), C_3117)=A_8 | r2_hidden(C_3117, k1_setfam_1(k1_tarski(A_8))) | k1_tarski(A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2124, c_14])).
% 5.92/2.27  tff(c_6526, plain, (![A_8095, C_8096]: ('#skF_4'(k1_tarski(A_8095), k1_setfam_1(k1_tarski(A_8095)), C_8096)=A_8095 | r2_hidden(C_8096, k1_setfam_1(k1_tarski(A_8095))))), inference(negUnitSimplification, [status(thm)], [c_6449, c_2155])).
% 5.92/2.27  tff(c_58, plain, (![C_36, A_24]: (~r2_hidden(C_36, '#skF_4'(A_24, k1_setfam_1(A_24), C_36)) | r2_hidden(C_36, k1_setfam_1(A_24)) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.92/2.27  tff(c_6535, plain, (![C_8096, A_8095]: (~r2_hidden(C_8096, A_8095) | r2_hidden(C_8096, k1_setfam_1(k1_tarski(A_8095))) | k1_tarski(A_8095)=k1_xboole_0 | r2_hidden(C_8096, k1_setfam_1(k1_tarski(A_8095))))), inference(superposition, [status(thm), theory('equality')], [c_6526, c_58])).
% 5.92/2.27  tff(c_6544, plain, (![C_8096, A_8095]: (~r2_hidden(C_8096, A_8095) | r2_hidden(C_8096, k1_setfam_1(k1_tarski(A_8095))) | r2_hidden(C_8096, k1_setfam_1(k1_tarski(A_8095))))), inference(negUnitSimplification, [status(thm)], [c_6449, c_6535])).
% 5.92/2.27  tff(c_6917, plain, (![C_8119, A_8120]: (~r2_hidden(C_8119, A_8120) | r2_hidden(C_8119, k1_setfam_1(k1_tarski(A_8120))))), inference(factorization, [status(thm), theory('equality')], [c_6544])).
% 5.92/2.27  tff(c_6980, plain, (![A_8124, A_8125]: (r1_tarski(A_8124, k1_setfam_1(k1_tarski(A_8125))) | ~r2_hidden('#skF_1'(A_8124, k1_setfam_1(k1_tarski(A_8125))), A_8125))), inference(resolution, [status(thm)], [c_6917, c_4])).
% 5.92/2.27  tff(c_7027, plain, (![A_1]: (r1_tarski(A_1, k1_setfam_1(k1_tarski(A_1))))), inference(resolution, [status(thm)], [c_6, c_6980])).
% 5.92/2.27  tff(c_1861, plain, (![C_3099, D_3100, A_3101]: (r2_hidden(C_3099, D_3100) | ~r2_hidden(D_3100, A_3101) | ~r2_hidden(C_3099, k1_setfam_1(A_3101)) | k1_xboole_0=A_3101)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.92/2.27  tff(c_1876, plain, (![C_3099, C_12]: (r2_hidden(C_3099, C_12) | ~r2_hidden(C_3099, k1_setfam_1(k1_tarski(C_12))) | k1_tarski(C_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1861])).
% 5.92/2.27  tff(c_6455, plain, (![C_8093, C_8094]: (r2_hidden(C_8093, C_8094) | ~r2_hidden(C_8093, k1_setfam_1(k1_tarski(C_8094))))), inference(negUnitSimplification, [status(thm)], [c_6449, c_1876])).
% 5.92/2.27  tff(c_6580, plain, (![C_8099, B_8100]: (r2_hidden('#skF_1'(k1_setfam_1(k1_tarski(C_8099)), B_8100), C_8099) | r1_tarski(k1_setfam_1(k1_tarski(C_8099)), B_8100))), inference(resolution, [status(thm)], [c_6, c_6455])).
% 5.92/2.27  tff(c_6620, plain, (![C_8101]: (r1_tarski(k1_setfam_1(k1_tarski(C_8101)), C_8101))), inference(resolution, [status(thm)], [c_6580, c_4])).
% 5.92/2.27  tff(c_6650, plain, (![C_8101]: (k1_setfam_1(k1_tarski(C_8101))=C_8101 | ~r1_tarski(C_8101, k1_setfam_1(k1_tarski(C_8101))))), inference(resolution, [status(thm)], [c_6620, c_8])).
% 5.92/2.27  tff(c_7056, plain, (![C_8101]: (k1_setfam_1(k1_tarski(C_8101))=C_8101)), inference(demodulation, [status(thm), theory('equality')], [c_7027, c_6650])).
% 5.92/2.27  tff(c_7102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7056, c_66])).
% 5.92/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.27  
% 5.92/2.27  Inference rules
% 5.92/2.27  ----------------------
% 5.92/2.27  #Ref     : 2
% 5.92/2.27  #Sup     : 1625
% 5.92/2.27  #Fact    : 4
% 5.92/2.27  #Define  : 0
% 5.92/2.27  #Split   : 7
% 5.92/2.27  #Chain   : 0
% 5.92/2.27  #Close   : 0
% 5.92/2.27  
% 5.92/2.27  Ordering : KBO
% 5.92/2.27  
% 5.92/2.27  Simplification rules
% 5.92/2.27  ----------------------
% 5.92/2.27  #Subsume      : 457
% 5.92/2.27  #Demod        : 188
% 5.92/2.27  #Tautology    : 219
% 5.92/2.27  #SimpNegUnit  : 151
% 5.92/2.27  #BackRed      : 12
% 5.92/2.27  
% 5.92/2.27  #Partial instantiations: 3645
% 5.92/2.27  #Strategies tried      : 1
% 5.92/2.27  
% 5.92/2.27  Timing (in seconds)
% 5.92/2.27  ----------------------
% 5.92/2.27  Preprocessing        : 0.35
% 5.92/2.27  Parsing              : 0.18
% 5.92/2.27  CNF conversion       : 0.03
% 5.92/2.27  Main loop            : 1.09
% 5.92/2.27  Inferencing          : 0.42
% 5.92/2.27  Reduction            : 0.28
% 5.92/2.27  Demodulation         : 0.17
% 5.92/2.27  BG Simplification    : 0.05
% 5.92/2.27  Subsumption          : 0.27
% 5.92/2.27  Abstraction          : 0.06
% 5.92/2.27  MUC search           : 0.00
% 5.92/2.27  Cooper               : 0.00
% 5.92/2.27  Total                : 1.48
% 5.92/2.27  Index Insertion      : 0.00
% 5.92/2.28  Index Deletion       : 0.00
% 5.92/2.28  Index Matching       : 0.00
% 5.92/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
