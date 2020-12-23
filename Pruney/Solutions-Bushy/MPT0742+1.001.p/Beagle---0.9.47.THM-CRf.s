%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0742+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:47 EST 2020

% Result     : Theorem 30.82s
% Output     : CNFRefutation 31.03s
% Verified   : 
% Statistics : Number of formulae       :  268 (2625 expanded)
%              Number of leaves         :   33 ( 851 expanded)
%              Depth                    :   33
%              Number of atoms          :  638 (6566 expanded)
%              Number of equality atoms :   62 ( 430 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > m1_subset_1 > v3_ordinal1 > v2_ordinal1 > v1_xboole_0 > v1_ordinal1 > #nlpp > o_1_0_ordinal1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(o_1_0_ordinal1,type,(
    o_1_0_ordinal1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B] :
        ( v3_ordinal1(B)
       => ~ ( r1_tarski(A,B)
            & A != k1_xboole_0
            & ! [C] :
                ( v3_ordinal1(C)
               => ~ ( r2_hidden(C,A)
                    & ! [D] :
                        ( v3_ordinal1(D)
                       => ( r2_hidden(D,A)
                         => r1_ordinal1(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(o_1_0_ordinal1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_ordinal1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_114,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => r1_ordinal1(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

tff(f_30,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_74,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_102036,plain,(
    ! [A_2033,C_2034,B_2035] :
      ( m1_subset_1(A_2033,C_2034)
      | ~ m1_subset_1(B_2035,k1_zfmisc_1(C_2034))
      | ~ r2_hidden(A_2033,B_2035) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_102060,plain,(
    ! [A_2038,B_2039,A_2040] :
      ( m1_subset_1(A_2038,B_2039)
      | ~ r2_hidden(A_2038,A_2040)
      | ~ r1_tarski(A_2040,B_2039) ) ),
    inference(resolution,[status(thm)],[c_28,c_102036])).

tff(c_102313,plain,(
    ! [A_2067,B_2068,B_2069] :
      ( m1_subset_1(A_2067,B_2068)
      | ~ r1_tarski(B_2069,B_2068)
      | v1_xboole_0(B_2069)
      | ~ m1_subset_1(A_2067,B_2069) ) ),
    inference(resolution,[status(thm)],[c_24,c_102060])).

tff(c_102334,plain,(
    ! [A_2067] :
      ( m1_subset_1(A_2067,'#skF_4')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_2067,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_102313])).

tff(c_102335,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_102334])).

tff(c_34,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_102338,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_102335,c_34])).

tff(c_102342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_102338])).

tff(c_102344,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_102334])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(o_1_0_ordinal1(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | v1_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_157,plain,(
    ! [B_69,A_70,A_71] :
      ( ~ v1_xboole_0(B_69)
      | ~ r2_hidden(A_70,A_71)
      | ~ r1_tarski(A_71,B_69) ) ),
    inference(resolution,[status(thm)],[c_28,c_132])).

tff(c_171,plain,(
    ! [B_73,A_74] :
      ( ~ v1_xboole_0(B_73)
      | ~ r1_tarski(A_74,B_73)
      | v1_ordinal1(A_74) ) ),
    inference(resolution,[status(thm)],[c_10,c_157])).

tff(c_179,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_171])).

tff(c_180,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_44,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_102345,plain,(
    ! [A_2070] :
      ( m1_subset_1(A_2070,'#skF_4')
      | ~ m1_subset_1(A_2070,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_102334])).

tff(c_102370,plain,(
    m1_subset_1(o_1_0_ordinal1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_102345])).

tff(c_108,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | v1_xboole_0(B_58)
      | ~ m1_subset_1(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( v3_ordinal1(A_11)
      | ~ r2_hidden(A_11,B_12)
      | ~ v3_ordinal1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_112,plain,(
    ! [A_57,B_58] :
      ( v3_ordinal1(A_57)
      | ~ v3_ordinal1(B_58)
      | v1_xboole_0(B_58)
      | ~ m1_subset_1(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_108,c_20])).

tff(c_102373,plain,
    ( v3_ordinal1(o_1_0_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_102370,c_112])).

tff(c_102376,plain,
    ( v3_ordinal1(o_1_0_ordinal1('#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_102373])).

tff(c_102377,plain,(
    v3_ordinal1(o_1_0_ordinal1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_102376])).

tff(c_48,plain,(
    ! [C_37] :
      ( r2_hidden('#skF_5'(C_37),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | ~ v3_ordinal1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_140,plain,(
    ! [C_66,A_67] :
      ( ~ v1_xboole_0(C_66)
      | ~ r2_hidden(A_67,o_1_0_ordinal1(k1_zfmisc_1(C_66))) ) ),
    inference(resolution,[status(thm)],[c_12,c_132])).

tff(c_102469,plain,(
    ! [C_2079,A_2080] :
      ( ~ v1_xboole_0(C_2079)
      | v1_xboole_0(o_1_0_ordinal1(k1_zfmisc_1(C_2079)))
      | ~ m1_subset_1(A_2080,o_1_0_ordinal1(k1_zfmisc_1(C_2079))) ) ),
    inference(resolution,[status(thm)],[c_24,c_140])).

tff(c_102494,plain,(
    ! [C_2081] :
      ( ~ v1_xboole_0(C_2081)
      | v1_xboole_0(o_1_0_ordinal1(k1_zfmisc_1(C_2081))) ) ),
    inference(resolution,[status(thm)],[c_12,c_102469])).

tff(c_102499,plain,(
    ! [C_2082] :
      ( o_1_0_ordinal1(k1_zfmisc_1(C_2082)) = k1_xboole_0
      | ~ v1_xboole_0(C_2082) ) ),
    inference(resolution,[status(thm)],[c_102494,c_34])).

tff(c_86,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_91,plain,(
    ! [B_50] : r1_tarski(o_1_0_ordinal1(k1_zfmisc_1(B_50)),B_50) ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_102564,plain,(
    ! [C_2085] :
      ( r1_tarski(k1_xboole_0,C_2085)
      | ~ v1_xboole_0(C_2085) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102499,c_91])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_ordinal1(A_7,B_8)
      | ~ r1_tarski(A_7,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102582,plain,(
    ! [C_2085] :
      ( r1_ordinal1(k1_xboole_0,C_2085)
      | ~ v3_ordinal1(C_2085)
      | ~ v3_ordinal1(k1_xboole_0)
      | ~ v1_xboole_0(C_2085) ) ),
    inference(resolution,[status(thm)],[c_102564,c_14])).

tff(c_109844,plain,(
    ~ v3_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_102582])).

tff(c_113,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(B_59,A_60)
      | ~ r2_hidden(B_59,A_60)
      | ~ v1_ordinal1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128,plain,(
    ! [C_37] :
      ( r1_tarski('#skF_5'(C_37),'#skF_3')
      | ~ v1_ordinal1('#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | ~ v3_ordinal1(C_37) ) ),
    inference(resolution,[status(thm)],[c_48,c_113])).

tff(c_220,plain,(
    ~ v1_ordinal1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_38,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_2'(A_27,B_28),B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_239,plain,(
    ! [A_90,C_91,B_92] :
      ( m1_subset_1(A_90,C_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(C_91))
      | ~ r2_hidden(A_90,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_263,plain,(
    ! [A_95,B_96,A_97] :
      ( m1_subset_1(A_95,B_96)
      | ~ r2_hidden(A_95,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(resolution,[status(thm)],[c_28,c_239])).

tff(c_626,plain,(
    ! [A_133,B_134,B_135] :
      ( m1_subset_1('#skF_2'(A_133,B_134),B_135)
      | ~ r1_tarski(B_134,B_135)
      | ~ r2_hidden(A_133,B_134) ) ),
    inference(resolution,[status(thm)],[c_38,c_263])).

tff(c_20761,plain,(
    ! [A_1180,B_1181,B_1182] :
      ( v3_ordinal1('#skF_2'(A_1180,B_1181))
      | ~ v3_ordinal1(B_1182)
      | v1_xboole_0(B_1182)
      | ~ r1_tarski(B_1181,B_1182)
      | ~ r2_hidden(A_1180,B_1181) ) ),
    inference(resolution,[status(thm)],[c_626,c_112])).

tff(c_20787,plain,(
    ! [A_1180] :
      ( v3_ordinal1('#skF_2'(A_1180,'#skF_3'))
      | ~ v3_ordinal1('#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_1180,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_20761])).

tff(c_20803,plain,(
    ! [A_1180] :
      ( v3_ordinal1('#skF_2'(A_1180,'#skF_3'))
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_1180,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20787])).

tff(c_20804,plain,(
    ! [A_1180] :
      ( v3_ordinal1('#skF_2'(A_1180,'#skF_3'))
      | ~ r2_hidden(A_1180,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_20803])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_ordinal1(A_9,A_9)
      | ~ v3_ordinal1(B_10)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_79,plain,(
    ! [B_10] : ~ v3_ordinal1(B_10) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_44])).

tff(c_84,plain,(
    ! [A_9] :
      ( r1_ordinal1(A_9,A_9)
      | ~ v3_ordinal1(A_9) ) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_63,plain,(
    ! [C_43] :
      ( v3_ordinal1('#skF_5'(C_43))
      | ~ r2_hidden(C_43,'#skF_3')
      | ~ v3_ordinal1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_ordinal1(A_1)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_71,plain,(
    ! [C_43] :
      ( v1_ordinal1('#skF_5'(C_43))
      | ~ r2_hidden(C_43,'#skF_3')
      | ~ v3_ordinal1(C_43) ) ),
    inference(resolution,[status(thm)],[c_63,c_4])).

tff(c_50,plain,(
    ! [C_37] :
      ( v3_ordinal1('#skF_5'(C_37))
      | ~ r2_hidden(C_37,'#skF_3')
      | ~ v3_ordinal1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_499,plain,(
    ! [B_120,A_121] :
      ( r2_hidden(B_120,A_121)
      | B_120 = A_121
      | r2_hidden(A_121,B_120)
      | ~ v3_ordinal1(B_120)
      | ~ v3_ordinal1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_5,A_2] :
      ( r1_tarski(B_5,A_2)
      | ~ r2_hidden(B_5,A_2)
      | ~ v1_ordinal1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_744,plain,(
    ! [B_141,A_142] :
      ( r1_tarski(B_141,A_142)
      | ~ v1_ordinal1(A_142)
      | B_141 = A_142
      | r2_hidden(A_142,B_141)
      | ~ v3_ordinal1(B_141)
      | ~ v3_ordinal1(A_142) ) ),
    inference(resolution,[status(thm)],[c_499,c_6])).

tff(c_36,plain,(
    ! [D_33,A_27,B_28] :
      ( ~ r2_hidden(D_33,'#skF_2'(A_27,B_28))
      | ~ r2_hidden(D_33,B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_26061,plain,(
    ! [A_1299,B_1300,A_1301] :
      ( ~ r2_hidden(A_1299,B_1300)
      | ~ r2_hidden(A_1301,B_1300)
      | r1_tarski('#skF_2'(A_1301,B_1300),A_1299)
      | ~ v1_ordinal1(A_1299)
      | A_1299 = '#skF_2'(A_1301,B_1300)
      | ~ v3_ordinal1('#skF_2'(A_1301,B_1300))
      | ~ v3_ordinal1(A_1299) ) ),
    inference(resolution,[status(thm)],[c_744,c_36])).

tff(c_84313,plain,(
    ! [A_1908,B_1909,A_1910] :
      ( r1_ordinal1('#skF_2'(A_1908,B_1909),A_1910)
      | ~ r2_hidden(A_1910,B_1909)
      | ~ r2_hidden(A_1908,B_1909)
      | ~ v1_ordinal1(A_1910)
      | A_1910 = '#skF_2'(A_1908,B_1909)
      | ~ v3_ordinal1('#skF_2'(A_1908,B_1909))
      | ~ v3_ordinal1(A_1910) ) ),
    inference(resolution,[status(thm)],[c_26061,c_14])).

tff(c_46,plain,(
    ! [C_37] :
      ( ~ r1_ordinal1(C_37,'#skF_5'(C_37))
      | ~ r2_hidden(C_37,'#skF_3')
      | ~ v3_ordinal1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_84664,plain,(
    ! [A_1912,B_1913] :
      ( ~ r2_hidden('#skF_2'(A_1912,B_1913),'#skF_3')
      | ~ r2_hidden('#skF_5'('#skF_2'(A_1912,B_1913)),B_1913)
      | ~ r2_hidden(A_1912,B_1913)
      | ~ v1_ordinal1('#skF_5'('#skF_2'(A_1912,B_1913)))
      | '#skF_5'('#skF_2'(A_1912,B_1913)) = '#skF_2'(A_1912,B_1913)
      | ~ v3_ordinal1('#skF_2'(A_1912,B_1913))
      | ~ v3_ordinal1('#skF_5'('#skF_2'(A_1912,B_1913))) ) ),
    inference(resolution,[status(thm)],[c_84313,c_46])).

tff(c_86620,plain,(
    ! [A_1924] :
      ( ~ r2_hidden(A_1924,'#skF_3')
      | ~ v1_ordinal1('#skF_5'('#skF_2'(A_1924,'#skF_3')))
      | '#skF_5'('#skF_2'(A_1924,'#skF_3')) = '#skF_2'(A_1924,'#skF_3')
      | ~ v3_ordinal1('#skF_5'('#skF_2'(A_1924,'#skF_3')))
      | ~ r2_hidden('#skF_2'(A_1924,'#skF_3'),'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_1924,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_84664])).

tff(c_87255,plain,(
    ! [A_1934] :
      ( ~ r2_hidden(A_1934,'#skF_3')
      | ~ v1_ordinal1('#skF_5'('#skF_2'(A_1934,'#skF_3')))
      | '#skF_5'('#skF_2'(A_1934,'#skF_3')) = '#skF_2'(A_1934,'#skF_3')
      | ~ r2_hidden('#skF_2'(A_1934,'#skF_3'),'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_1934,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_50,c_86620])).

tff(c_88932,plain,(
    ! [A_1957] :
      ( ~ r2_hidden(A_1957,'#skF_3')
      | '#skF_5'('#skF_2'(A_1957,'#skF_3')) = '#skF_2'(A_1957,'#skF_3')
      | ~ r2_hidden('#skF_2'(A_1957,'#skF_3'),'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_1957,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_71,c_87255])).

tff(c_98892,plain,(
    ! [A_2013] :
      ( '#skF_5'('#skF_2'(A_2013,'#skF_3')) = '#skF_2'(A_2013,'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_2013,'#skF_3'))
      | ~ r2_hidden(A_2013,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_88932])).

tff(c_99443,plain,(
    ! [A_2017] :
      ( '#skF_5'('#skF_2'(A_2017,'#skF_3')) = '#skF_2'(A_2017,'#skF_3')
      | ~ r2_hidden(A_2017,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20804,c_98892])).

tff(c_100729,plain,(
    ! [A_2019] :
      ( ~ r1_ordinal1('#skF_2'(A_2019,'#skF_3'),'#skF_2'(A_2019,'#skF_3'))
      | ~ r2_hidden('#skF_2'(A_2019,'#skF_3'),'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_2019,'#skF_3'))
      | ~ r2_hidden(A_2019,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99443,c_46])).

tff(c_101566,plain,(
    ! [A_2023] :
      ( ~ r2_hidden('#skF_2'(A_2023,'#skF_3'),'#skF_3')
      | ~ r2_hidden(A_2023,'#skF_3')
      | ~ v3_ordinal1('#skF_2'(A_2023,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_84,c_100729])).

tff(c_101727,plain,(
    ! [A_2024] :
      ( ~ v3_ordinal1('#skF_2'(A_2024,'#skF_3'))
      | ~ r2_hidden(A_2024,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_101566])).

tff(c_101889,plain,(
    ! [A_2025] : ~ r2_hidden(A_2025,'#skF_3') ),
    inference(resolution,[status(thm)],[c_20804,c_101727])).

tff(c_101977,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_101889])).

tff(c_102006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_101977])).

tff(c_102008,plain,(
    v1_ordinal1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_127,plain,(
    ! [A_27,B_28] :
      ( r1_tarski('#skF_2'(A_27,B_28),B_28)
      | ~ v1_ordinal1(B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_38,c_113])).

tff(c_102070,plain,(
    ! [A_27,B_28,B_2039] :
      ( m1_subset_1('#skF_2'(A_27,B_28),B_2039)
      | ~ r1_tarski(B_28,B_2039)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_38,c_102060])).

tff(c_102100,plain,(
    ! [D_2045,A_2046,B_2047] :
      ( ~ r2_hidden(D_2045,'#skF_2'(A_2046,B_2047))
      | ~ r2_hidden(D_2045,B_2047)
      | ~ r2_hidden(A_2046,B_2047) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_109814,plain,(
    ! [A_2587,A_2588,B_2589] :
      ( ~ r2_hidden('#skF_2'(A_2587,'#skF_2'(A_2588,B_2589)),B_2589)
      | ~ r2_hidden(A_2588,B_2589)
      | ~ r2_hidden(A_2587,'#skF_2'(A_2588,B_2589)) ) ),
    inference(resolution,[status(thm)],[c_38,c_102100])).

tff(c_112311,plain,(
    ! [A_2750,B_2751,A_2752] :
      ( ~ r2_hidden(A_2750,B_2751)
      | ~ r2_hidden(A_2752,'#skF_2'(A_2750,B_2751))
      | v1_xboole_0(B_2751)
      | ~ m1_subset_1('#skF_2'(A_2752,'#skF_2'(A_2750,B_2751)),B_2751) ) ),
    inference(resolution,[status(thm)],[c_24,c_109814])).

tff(c_115116,plain,(
    ! [A_2827,B_2828,A_2829] :
      ( ~ r2_hidden(A_2827,B_2828)
      | v1_xboole_0(B_2828)
      | ~ r1_tarski('#skF_2'(A_2827,B_2828),B_2828)
      | ~ r2_hidden(A_2829,'#skF_2'(A_2827,B_2828)) ) ),
    inference(resolution,[status(thm)],[c_102070,c_112311])).

tff(c_115140,plain,(
    ! [B_2830,A_2831,A_2832] :
      ( v1_xboole_0(B_2830)
      | ~ r2_hidden(A_2831,'#skF_2'(A_2832,B_2830))
      | ~ v1_ordinal1(B_2830)
      | ~ r2_hidden(A_2832,B_2830) ) ),
    inference(resolution,[status(thm)],[c_127,c_115116])).

tff(c_120496,plain,(
    ! [B_3058,A_3059,A_3060] :
      ( v1_xboole_0(B_3058)
      | ~ v1_ordinal1(B_3058)
      | ~ r2_hidden(A_3059,B_3058)
      | v1_xboole_0('#skF_2'(A_3059,B_3058))
      | ~ m1_subset_1(A_3060,'#skF_2'(A_3059,B_3058)) ) ),
    inference(resolution,[status(thm)],[c_24,c_115140])).

tff(c_120579,plain,(
    ! [B_3061,A_3062] :
      ( v1_xboole_0(B_3061)
      | ~ v1_ordinal1(B_3061)
      | ~ r2_hidden(A_3062,B_3061)
      | v1_xboole_0('#skF_2'(A_3062,B_3061)) ) ),
    inference(resolution,[status(thm)],[c_12,c_120496])).

tff(c_120588,plain,(
    ! [A_3063,B_3064] :
      ( '#skF_2'(A_3063,B_3064) = k1_xboole_0
      | v1_xboole_0(B_3064)
      | ~ v1_ordinal1(B_3064)
      | ~ r2_hidden(A_3063,B_3064) ) ),
    inference(resolution,[status(thm)],[c_120579,c_34])).

tff(c_120621,plain,(
    ! [C_37] :
      ( '#skF_2'('#skF_5'(C_37),'#skF_3') = k1_xboole_0
      | v1_xboole_0('#skF_3')
      | ~ v1_ordinal1('#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | ~ v3_ordinal1(C_37) ) ),
    inference(resolution,[status(thm)],[c_48,c_120588])).

tff(c_120637,plain,(
    ! [C_37] :
      ( '#skF_2'('#skF_5'(C_37),'#skF_3') = k1_xboole_0
      | v1_xboole_0('#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | ~ v3_ordinal1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102008,c_120621])).

tff(c_120640,plain,(
    ! [C_3065] :
      ( '#skF_2'('#skF_5'(C_3065),'#skF_3') = k1_xboole_0
      | ~ r2_hidden(C_3065,'#skF_3')
      | ~ v3_ordinal1(C_3065) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_120637])).

tff(c_102219,plain,(
    ! [A_2060,B_2061,B_2062] :
      ( m1_subset_1('#skF_2'(A_2060,B_2061),B_2062)
      | ~ r1_tarski(B_2061,B_2062)
      | ~ r2_hidden(A_2060,B_2061) ) ),
    inference(resolution,[status(thm)],[c_38,c_102060])).

tff(c_110871,plain,(
    ! [A_2672,B_2673,B_2674] :
      ( v3_ordinal1('#skF_2'(A_2672,B_2673))
      | ~ v3_ordinal1(B_2674)
      | v1_xboole_0(B_2674)
      | ~ r1_tarski(B_2673,B_2674)
      | ~ r2_hidden(A_2672,B_2673) ) ),
    inference(resolution,[status(thm)],[c_102219,c_112])).

tff(c_110897,plain,(
    ! [A_2672] :
      ( v3_ordinal1('#skF_2'(A_2672,'#skF_3'))
      | ~ v3_ordinal1('#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_2672,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_110871])).

tff(c_110914,plain,(
    ! [A_2672] :
      ( v3_ordinal1('#skF_2'(A_2672,'#skF_3'))
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_2672,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_110897])).

tff(c_110915,plain,(
    ! [A_2672] :
      ( v3_ordinal1('#skF_2'(A_2672,'#skF_3'))
      | ~ r2_hidden(A_2672,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_110914])).

tff(c_120719,plain,(
    ! [C_3065] :
      ( v3_ordinal1(k1_xboole_0)
      | ~ r2_hidden('#skF_5'(C_3065),'#skF_3')
      | ~ r2_hidden(C_3065,'#skF_3')
      | ~ v3_ordinal1(C_3065) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120640,c_110915])).

tff(c_120822,plain,(
    ! [C_3066] :
      ( ~ r2_hidden('#skF_5'(C_3066),'#skF_3')
      | ~ r2_hidden(C_3066,'#skF_3')
      | ~ v3_ordinal1(C_3066) ) ),
    inference(negUnitSimplification,[status(thm)],[c_109844,c_120719])).

tff(c_120849,plain,(
    ! [C_3067] :
      ( ~ r2_hidden(C_3067,'#skF_3')
      | ~ v3_ordinal1(C_3067) ) ),
    inference(resolution,[status(thm)],[c_48,c_120822])).

tff(c_120881,plain,(
    ! [A_16] :
      ( ~ v3_ordinal1(A_16)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_16,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_120849])).

tff(c_120903,plain,(
    ! [A_3068] :
      ( ~ v3_ordinal1(A_3068)
      | ~ m1_subset_1(A_3068,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_120881])).

tff(c_120959,plain,(
    ~ v3_ordinal1(o_1_0_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_120903])).

tff(c_120987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102377,c_120959])).

tff(c_120989,plain,(
    v3_ordinal1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_102582])).

tff(c_53,plain,(
    ! [A_41] :
      ( v1_ordinal1(A_41)
      | ~ v3_ordinal1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_57,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_53])).

tff(c_107673,plain,(
    ! [C_2429] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(C_2429))
      | ~ v1_xboole_0(C_2429) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102499,c_12])).

tff(c_32,plain,(
    ! [C_25,B_24,A_23] :
      ( ~ v1_xboole_0(C_25)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(C_25))
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_107686,plain,(
    ! [A_23,C_2429] :
      ( ~ r2_hidden(A_23,k1_xboole_0)
      | ~ v1_xboole_0(C_2429) ) ),
    inference(resolution,[status(thm)],[c_107673,c_32])).

tff(c_107688,plain,(
    ! [C_2429] : ~ v1_xboole_0(C_2429) ),
    inference(splitLeft,[status(thm)],[c_107686])).

tff(c_107710,plain,(
    ! [A_2433,B_2434] :
      ( r2_hidden(A_2433,B_2434)
      | ~ m1_subset_1(A_2433,B_2434) ) ),
    inference(negUnitSimplification,[status(thm)],[c_107688,c_24])).

tff(c_102043,plain,(
    ! [A_2033,C_2034] :
      ( m1_subset_1(A_2033,C_2034)
      | ~ r2_hidden(A_2033,o_1_0_ordinal1(k1_zfmisc_1(C_2034))) ) ),
    inference(resolution,[status(thm)],[c_12,c_102036])).

tff(c_107824,plain,(
    ! [A_2445,C_2446] :
      ( m1_subset_1(A_2445,C_2446)
      | ~ m1_subset_1(A_2445,o_1_0_ordinal1(k1_zfmisc_1(C_2446))) ) ),
    inference(resolution,[status(thm)],[c_107710,c_102043])).

tff(c_107859,plain,(
    ! [C_2449] : m1_subset_1(o_1_0_ordinal1(o_1_0_ordinal1(k1_zfmisc_1(C_2449))),C_2449) ),
    inference(resolution,[status(thm)],[c_12,c_107824])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_107882,plain,(
    ! [B_19] : r1_tarski(o_1_0_ordinal1(o_1_0_ordinal1(k1_zfmisc_1(k1_zfmisc_1(B_19)))),B_19) ),
    inference(resolution,[status(thm)],[c_107859,c_26])).

tff(c_102069,plain,(
    ! [A_16,B_2039,B_17] :
      ( m1_subset_1(A_16,B_2039)
      | ~ r1_tarski(B_17,B_2039)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_102060])).

tff(c_108080,plain,(
    ! [A_2464,B_2465,B_2466] :
      ( m1_subset_1(A_2464,B_2465)
      | ~ r1_tarski(B_2466,B_2465)
      | ~ m1_subset_1(A_2464,B_2466) ) ),
    inference(negUnitSimplification,[status(thm)],[c_107688,c_102069])).

tff(c_108353,plain,(
    ! [A_2492,B_2493] :
      ( m1_subset_1(A_2492,B_2493)
      | ~ m1_subset_1(A_2492,o_1_0_ordinal1(o_1_0_ordinal1(k1_zfmisc_1(k1_zfmisc_1(B_2493))))) ) ),
    inference(resolution,[status(thm)],[c_107882,c_108080])).

tff(c_108389,plain,(
    ! [B_2494] : m1_subset_1(o_1_0_ordinal1(o_1_0_ordinal1(o_1_0_ordinal1(k1_zfmisc_1(k1_zfmisc_1(B_2494))))),B_2494) ),
    inference(resolution,[status(thm)],[c_12,c_108353])).

tff(c_107734,plain,(
    ! [A_2433,C_2034] :
      ( m1_subset_1(A_2433,C_2034)
      | ~ m1_subset_1(A_2433,o_1_0_ordinal1(k1_zfmisc_1(C_2034))) ) ),
    inference(resolution,[status(thm)],[c_107710,c_102043])).

tff(c_108652,plain,(
    ! [C_2518] : m1_subset_1(o_1_0_ordinal1(o_1_0_ordinal1(o_1_0_ordinal1(k1_zfmisc_1(k1_zfmisc_1(o_1_0_ordinal1(k1_zfmisc_1(C_2518))))))),C_2518) ),
    inference(resolution,[status(thm)],[c_108389,c_107734])).

tff(c_102343,plain,(
    ! [A_2067] :
      ( m1_subset_1(A_2067,'#skF_4')
      | ~ m1_subset_1(A_2067,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_102334])).

tff(c_108688,plain,(
    m1_subset_1(o_1_0_ordinal1(o_1_0_ordinal1(o_1_0_ordinal1(k1_zfmisc_1(k1_zfmisc_1(o_1_0_ordinal1(k1_zfmisc_1('#skF_3'))))))),'#skF_4') ),
    inference(resolution,[status(thm)],[c_108652,c_102343])).

tff(c_107698,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(negUnitSimplification,[status(thm)],[c_107688,c_24])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_ordinal1(A_7,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107735,plain,(
    ! [A_2433,B_2434] :
      ( r1_tarski(A_2433,B_2434)
      | ~ v1_ordinal1(B_2434)
      | ~ m1_subset_1(A_2433,B_2434) ) ),
    inference(resolution,[status(thm)],[c_107710,c_6])).

tff(c_108828,plain,(
    ! [A_2526,B_2527,A_2528] :
      ( m1_subset_1(A_2526,B_2527)
      | ~ m1_subset_1(A_2526,A_2528)
      | ~ v1_ordinal1(B_2527)
      | ~ m1_subset_1(A_2528,B_2527) ) ),
    inference(resolution,[status(thm)],[c_107735,c_108080])).

tff(c_108901,plain,(
    ! [A_2529,B_2530] :
      ( m1_subset_1(o_1_0_ordinal1(A_2529),B_2530)
      | ~ v1_ordinal1(B_2530)
      | ~ m1_subset_1(A_2529,B_2530) ) ),
    inference(resolution,[status(thm)],[c_12,c_108828])).

tff(c_107897,plain,(
    ! [A_2450,B_2451,A_2452] :
      ( ~ r2_hidden(A_2450,B_2451)
      | ~ r2_hidden(A_2452,B_2451)
      | ~ m1_subset_1(A_2450,'#skF_2'(A_2452,B_2451)) ) ),
    inference(resolution,[status(thm)],[c_107710,c_36])).

tff(c_108129,plain,(
    ! [A_2470,B_2471] :
      ( ~ r2_hidden(o_1_0_ordinal1('#skF_2'(A_2470,B_2471)),B_2471)
      | ~ r2_hidden(A_2470,B_2471) ) ),
    inference(resolution,[status(thm)],[c_12,c_107897])).

tff(c_108146,plain,(
    ! [A_2470,B_17] :
      ( ~ r2_hidden(A_2470,B_17)
      | ~ m1_subset_1(o_1_0_ordinal1('#skF_2'(A_2470,B_17)),B_17) ) ),
    inference(resolution,[status(thm)],[c_107698,c_108129])).

tff(c_109171,plain,(
    ! [A_2540,B_2541] :
      ( ~ r2_hidden(A_2540,B_2541)
      | ~ v1_ordinal1(B_2541)
      | ~ m1_subset_1('#skF_2'(A_2540,B_2541),B_2541) ) ),
    inference(resolution,[status(thm)],[c_108901,c_108146])).

tff(c_109215,plain,(
    ! [B_2543,A_2544] :
      ( ~ v1_ordinal1(B_2543)
      | ~ r1_tarski(B_2543,B_2543)
      | ~ r2_hidden(A_2544,B_2543) ) ),
    inference(resolution,[status(thm)],[c_102070,c_109171])).

tff(c_109564,plain,(
    ! [B_2571,A_2572] :
      ( ~ v1_ordinal1(B_2571)
      | ~ r2_hidden(A_2572,B_2571)
      | ~ r1_ordinal1(B_2571,B_2571)
      | ~ v3_ordinal1(B_2571) ) ),
    inference(resolution,[status(thm)],[c_16,c_109215])).

tff(c_109617,plain,(
    ! [B_2578,A_2579] :
      ( ~ v1_ordinal1(B_2578)
      | ~ r1_ordinal1(B_2578,B_2578)
      | ~ v3_ordinal1(B_2578)
      | ~ m1_subset_1(A_2579,B_2578) ) ),
    inference(resolution,[status(thm)],[c_107698,c_109564])).

tff(c_109625,plain,(
    ! [A_2580,A_2581] :
      ( ~ v1_ordinal1(A_2580)
      | ~ m1_subset_1(A_2581,A_2580)
      | ~ v3_ordinal1(A_2580) ) ),
    inference(resolution,[status(thm)],[c_84,c_109617])).

tff(c_109640,plain,
    ( ~ v1_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_108688,c_109625])).

tff(c_109721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_57,c_109640])).

tff(c_109748,plain,(
    ! [A_2585] : ~ r2_hidden(A_2585,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_107686])).

tff(c_109776,plain,(
    ! [A_16] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_109748])).

tff(c_109781,plain,(
    ! [A_2586] : ~ m1_subset_1(A_2586,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_109776])).

tff(c_109806,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_109781])).

tff(c_109807,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_109776])).

tff(c_22,plain,(
    ! [B_15,A_13] :
      ( r2_hidden(B_15,A_13)
      | B_15 = A_13
      | r2_hidden(A_13,B_15)
      | ~ v3_ordinal1(B_15)
      | ~ v3_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_109774,plain,(
    ! [B_15] :
      ( k1_xboole_0 = B_15
      | r2_hidden(k1_xboole_0,B_15)
      | ~ v3_ordinal1(B_15)
      | ~ v3_ordinal1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_109748])).

tff(c_121036,plain,(
    ! [B_3073] :
      ( k1_xboole_0 = B_3073
      | r2_hidden(k1_xboole_0,B_3073)
      | ~ v3_ordinal1(B_3073) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120989,c_109774])).

tff(c_121122,plain,(
    ! [B_3076] :
      ( r1_tarski(k1_xboole_0,B_3076)
      | ~ v1_ordinal1(B_3076)
      | k1_xboole_0 = B_3076
      | ~ v3_ordinal1(B_3076) ) ),
    inference(resolution,[status(thm)],[c_121036,c_6])).

tff(c_121136,plain,(
    ! [B_3076] :
      ( r1_ordinal1(k1_xboole_0,B_3076)
      | ~ v3_ordinal1(k1_xboole_0)
      | ~ v1_ordinal1(B_3076)
      | k1_xboole_0 = B_3076
      | ~ v3_ordinal1(B_3076) ) ),
    inference(resolution,[status(thm)],[c_121122,c_14])).

tff(c_121200,plain,(
    ! [B_3080] :
      ( r1_ordinal1(k1_xboole_0,B_3080)
      | ~ v1_ordinal1(B_3080)
      | k1_xboole_0 = B_3080
      | ~ v3_ordinal1(B_3080) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120989,c_121136])).

tff(c_121204,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_3')
    | ~ v3_ordinal1(k1_xboole_0)
    | ~ v1_ordinal1('#skF_5'(k1_xboole_0))
    | '#skF_5'(k1_xboole_0) = k1_xboole_0
    | ~ v3_ordinal1('#skF_5'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_121200,c_46])).

tff(c_121207,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_3')
    | ~ v1_ordinal1('#skF_5'(k1_xboole_0))
    | '#skF_5'(k1_xboole_0) = k1_xboole_0
    | ~ v3_ordinal1('#skF_5'(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120989,c_121204])).

tff(c_121210,plain,(
    ~ v3_ordinal1('#skF_5'(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_121207])).

tff(c_121213,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_3')
    | ~ v3_ordinal1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_121210])).

tff(c_121216,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120989,c_121213])).

tff(c_121231,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_121216])).

tff(c_121248,plain,(
    ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_121231])).

tff(c_102007,plain,(
    ! [C_37] :
      ( r1_tarski('#skF_5'(C_37),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | ~ v3_ordinal1(C_37) ) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_102042,plain,(
    ! [A_2033,B_19,A_18] :
      ( m1_subset_1(A_2033,B_19)
      | ~ r2_hidden(A_2033,A_18)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_28,c_102036])).

tff(c_121283,plain,(
    ! [B_3090,B_3091] :
      ( m1_subset_1(k1_xboole_0,B_3090)
      | ~ r1_tarski(B_3091,B_3090)
      | k1_xboole_0 = B_3091
      | ~ v3_ordinal1(B_3091) ) ),
    inference(resolution,[status(thm)],[c_121036,c_102042])).

tff(c_121304,plain,(
    ! [C_37] :
      ( m1_subset_1(k1_xboole_0,'#skF_3')
      | '#skF_5'(C_37) = k1_xboole_0
      | ~ v3_ordinal1('#skF_5'(C_37))
      | ~ r2_hidden(C_37,'#skF_3')
      | ~ v3_ordinal1(C_37) ) ),
    inference(resolution,[status(thm)],[c_102007,c_121283])).

tff(c_121898,plain,(
    ! [C_3110] :
      ( '#skF_5'(C_3110) = k1_xboole_0
      | ~ v3_ordinal1('#skF_5'(C_3110))
      | ~ r2_hidden(C_3110,'#skF_3')
      | ~ v3_ordinal1(C_3110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_121248,c_121304])).

tff(c_121903,plain,(
    ! [C_3111] :
      ( '#skF_5'(C_3111) = k1_xboole_0
      | ~ r2_hidden(C_3111,'#skF_3')
      | ~ v3_ordinal1(C_3111) ) ),
    inference(resolution,[status(thm)],[c_50,c_121898])).

tff(c_121927,plain,(
    ! [A_16] :
      ( '#skF_5'(A_16) = k1_xboole_0
      | ~ v3_ordinal1(A_16)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_16,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_121903])).

tff(c_121959,plain,(
    ! [A_3113] :
      ( '#skF_5'(A_3113) = k1_xboole_0
      | ~ v3_ordinal1(A_3113)
      | ~ m1_subset_1(A_3113,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_121927])).

tff(c_121987,plain,
    ( '#skF_5'(o_1_0_ordinal1('#skF_3')) = k1_xboole_0
    | ~ v3_ordinal1(o_1_0_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_121959])).

tff(c_121999,plain,(
    '#skF_5'(o_1_0_ordinal1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102377,c_121987])).

tff(c_122028,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | ~ r2_hidden(o_1_0_ordinal1('#skF_3'),'#skF_3')
    | ~ v3_ordinal1(o_1_0_ordinal1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121999,c_48])).

tff(c_122053,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | ~ r2_hidden(o_1_0_ordinal1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102377,c_122028])).

tff(c_122054,plain,(
    ~ r2_hidden(o_1_0_ordinal1('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_121216,c_122053])).

tff(c_122069,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(o_1_0_ordinal1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_122054])).

tff(c_122081,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_122069])).

tff(c_122083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_122081])).

tff(c_122085,plain,(
    v3_ordinal1('#skF_5'(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_121207])).

tff(c_122093,plain,(
    v1_ordinal1('#skF_5'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_122085,c_4])).

tff(c_122084,plain,
    ( ~ v1_ordinal1('#skF_5'(k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,'#skF_3')
    | '#skF_5'(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_121207])).

tff(c_122095,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_3')
    | '#skF_5'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122093,c_122084])).

tff(c_122096,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_122095])).

tff(c_122111,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_122096])).

tff(c_122128,plain,(
    ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_122111])).

tff(c_122574,plain,(
    ! [B_3131,B_3132] :
      ( m1_subset_1(k1_xboole_0,B_3131)
      | ~ r1_tarski(B_3132,B_3131)
      | k1_xboole_0 = B_3132
      | ~ v3_ordinal1(B_3132) ) ),
    inference(resolution,[status(thm)],[c_121036,c_102042])).

tff(c_122598,plain,(
    ! [C_37] :
      ( m1_subset_1(k1_xboole_0,'#skF_3')
      | '#skF_5'(C_37) = k1_xboole_0
      | ~ v3_ordinal1('#skF_5'(C_37))
      | ~ r2_hidden(C_37,'#skF_3')
      | ~ v3_ordinal1(C_37) ) ),
    inference(resolution,[status(thm)],[c_102007,c_122574])).

tff(c_122784,plain,(
    ! [C_3145] :
      ( '#skF_5'(C_3145) = k1_xboole_0
      | ~ v3_ordinal1('#skF_5'(C_3145))
      | ~ r2_hidden(C_3145,'#skF_3')
      | ~ v3_ordinal1(C_3145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122128,c_122598])).

tff(c_122805,plain,(
    ! [C_3148] :
      ( '#skF_5'(C_3148) = k1_xboole_0
      | ~ r2_hidden(C_3148,'#skF_3')
      | ~ v3_ordinal1(C_3148) ) ),
    inference(resolution,[status(thm)],[c_50,c_122784])).

tff(c_122829,plain,(
    ! [A_16] :
      ( '#skF_5'(A_16) = k1_xboole_0
      | ~ v3_ordinal1(A_16)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_16,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_122805])).

tff(c_122856,plain,(
    ! [A_3149] :
      ( '#skF_5'(A_3149) = k1_xboole_0
      | ~ v3_ordinal1(A_3149)
      | ~ m1_subset_1(A_3149,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_122829])).

tff(c_122884,plain,
    ( '#skF_5'(o_1_0_ordinal1('#skF_3')) = k1_xboole_0
    | ~ v3_ordinal1(o_1_0_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_122856])).

tff(c_122896,plain,(
    '#skF_5'(o_1_0_ordinal1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102377,c_122884])).

tff(c_122922,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | ~ r2_hidden(o_1_0_ordinal1('#skF_3'),'#skF_3')
    | ~ v3_ordinal1(o_1_0_ordinal1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_122896,c_48])).

tff(c_122945,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | ~ r2_hidden(o_1_0_ordinal1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102377,c_122922])).

tff(c_122946,plain,(
    ~ r2_hidden(o_1_0_ordinal1('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_122096,c_122945])).

tff(c_122977,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(o_1_0_ordinal1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_122946])).

tff(c_122989,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_122977])).

tff(c_122991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_122989])).

tff(c_122992,plain,(
    '#skF_5'(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_122095])).

tff(c_121025,plain,(
    ! [C_3072] :
      ( r1_ordinal1(k1_xboole_0,C_3072)
      | ~ v3_ordinal1(C_3072)
      | ~ v1_xboole_0(C_3072) ) ),
    inference(splitRight,[status(thm)],[c_102582])).

tff(c_121029,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_3')
    | ~ v3_ordinal1(k1_xboole_0)
    | ~ v3_ordinal1('#skF_5'(k1_xboole_0))
    | ~ v1_xboole_0('#skF_5'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_121025,c_46])).

tff(c_121032,plain,
    ( ~ r2_hidden(k1_xboole_0,'#skF_3')
    | ~ v3_ordinal1('#skF_5'(k1_xboole_0))
    | ~ v1_xboole_0('#skF_5'(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120989,c_121029])).

tff(c_121033,plain,(
    ~ v1_xboole_0('#skF_5'(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_121032])).

tff(c_122997,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122992,c_121033])).

tff(c_123003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109807,c_122997])).

tff(c_123005,plain,(
    v1_xboole_0('#skF_5'(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_121032])).

tff(c_123009,plain,(
    '#skF_5'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123005,c_34])).

tff(c_123004,plain,
    ( ~ v3_ordinal1('#skF_5'(k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_121032])).

tff(c_123061,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120989,c_123009,c_123004])).

tff(c_123073,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_123061])).

tff(c_123088,plain,(
    ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_123073])).

tff(c_123161,plain,(
    ! [B_3157] :
      ( k1_xboole_0 = B_3157
      | r2_hidden(k1_xboole_0,B_3157)
      | ~ v3_ordinal1(B_3157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120989,c_109774])).

tff(c_123413,plain,(
    ! [B_3172,B_3173] :
      ( m1_subset_1(k1_xboole_0,B_3172)
      | ~ r1_tarski(B_3173,B_3172)
      | k1_xboole_0 = B_3173
      | ~ v3_ordinal1(B_3173) ) ),
    inference(resolution,[status(thm)],[c_123161,c_102042])).

tff(c_123434,plain,(
    ! [C_37] :
      ( m1_subset_1(k1_xboole_0,'#skF_3')
      | '#skF_5'(C_37) = k1_xboole_0
      | ~ v3_ordinal1('#skF_5'(C_37))
      | ~ r2_hidden(C_37,'#skF_3')
      | ~ v3_ordinal1(C_37) ) ),
    inference(resolution,[status(thm)],[c_102007,c_123413])).

tff(c_123820,plain,(
    ! [C_3190] :
      ( '#skF_5'(C_3190) = k1_xboole_0
      | ~ v3_ordinal1('#skF_5'(C_3190))
      | ~ r2_hidden(C_3190,'#skF_3')
      | ~ v3_ordinal1(C_3190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123088,c_123434])).

tff(c_123830,plain,(
    ! [C_3191] :
      ( '#skF_5'(C_3191) = k1_xboole_0
      | ~ r2_hidden(C_3191,'#skF_3')
      | ~ v3_ordinal1(C_3191) ) ),
    inference(resolution,[status(thm)],[c_50,c_123820])).

tff(c_123854,plain,(
    ! [A_16] :
      ( '#skF_5'(A_16) = k1_xboole_0
      | ~ v3_ordinal1(A_16)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_16,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_123830])).

tff(c_123881,plain,(
    ! [A_3192] :
      ( '#skF_5'(A_3192) = k1_xboole_0
      | ~ v3_ordinal1(A_3192)
      | ~ m1_subset_1(A_3192,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_123854])).

tff(c_123909,plain,
    ( '#skF_5'(o_1_0_ordinal1('#skF_3')) = k1_xboole_0
    | ~ v3_ordinal1(o_1_0_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_123881])).

tff(c_123921,plain,(
    '#skF_5'(o_1_0_ordinal1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102377,c_123909])).

tff(c_123947,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | ~ r2_hidden(o_1_0_ordinal1('#skF_3'),'#skF_3')
    | ~ v3_ordinal1(o_1_0_ordinal1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_123921,c_48])).

tff(c_123970,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | ~ r2_hidden(o_1_0_ordinal1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102377,c_123947])).

tff(c_123971,plain,(
    ~ r2_hidden(o_1_0_ordinal1('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_123061,c_123970])).

tff(c_123986,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(o_1_0_ordinal1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_123971])).

tff(c_123998,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_123986])).

tff(c_124000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102344,c_123998])).

tff(c_124002,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_124017,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_124002,c_34])).

tff(c_124019,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124017,c_40])).

tff(c_124199,plain,(
    ! [B_3229,B_3230,A_3231] :
      ( ~ v1_xboole_0(B_3229)
      | ~ r1_tarski(B_3230,B_3229)
      | v1_xboole_0(B_3230)
      | ~ m1_subset_1(A_3231,B_3230) ) ),
    inference(resolution,[status(thm)],[c_24,c_157])).

tff(c_124211,plain,(
    ! [A_3231] :
      ( ~ v1_xboole_0('#skF_4')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_3231,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_124199])).

tff(c_124219,plain,(
    ! [A_3231] :
      ( v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_3231,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124002,c_124211])).

tff(c_124221,plain,(
    ! [A_3232] : ~ m1_subset_1(A_3232,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_124219])).

tff(c_124236,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_124221])).

tff(c_124237,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_124219])).

tff(c_124018,plain,(
    ! [A_26] :
      ( A_26 = '#skF_4'
      | ~ v1_xboole_0(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124017,c_34])).

tff(c_124240,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_124237,c_124018])).

tff(c_124244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124019,c_124240])).

%------------------------------------------------------------------------------
