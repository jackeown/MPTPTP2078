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
% DateTime   : Thu Dec  3 10:28:15 EST 2020

% Result     : Theorem 8.82s
% Output     : CNFRefutation 9.11s
% Verified   : 
% Statistics : Number of formulae       :  130 (1015 expanded)
%              Number of leaves         :   35 ( 355 expanded)
%              Depth                    :   28
%              Number of atoms          :  215 (2206 expanded)
%              Number of equality atoms :   84 ( 750 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_46,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_44,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_201,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,B_53) = B_53
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_205,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_201])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_210,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_2])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_216,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_18])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_390,plain,(
    ! [B_71,A_72] :
      ( ~ r1_xboole_0(B_71,A_72)
      | ~ r1_tarski(B_71,A_72)
      | v1_xboole_0(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_580,plain,(
    ! [A_97,B_98] :
      ( ~ r1_tarski(A_97,B_98)
      | v1_xboole_0(A_97)
      | k4_xboole_0(A_97,B_98) != A_97 ) ),
    inference(resolution,[status(thm)],[c_24,c_390])).

tff(c_589,plain,
    ( v1_xboole_0('#skF_5')
    | k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_580])).

tff(c_594,plain,
    ( v1_xboole_0('#skF_5')
    | k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_589])).

tff(c_595,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_594])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    ! [A_31] :
      ( m1_subset_1('#skF_4'(A_31),A_31)
      | ~ v1_zfmisc_1(A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_596,plain,(
    ! [A_99,B_100] :
      ( k6_domain_1(A_99,B_100) = k1_tarski(B_100)
      | ~ m1_subset_1(B_100,A_99)
      | v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1654,plain,(
    ! [A_161] :
      ( k6_domain_1(A_161,'#skF_4'(A_161)) = k1_tarski('#skF_4'(A_161))
      | ~ v1_zfmisc_1(A_161)
      | v1_xboole_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_42,c_596])).

tff(c_40,plain,(
    ! [A_31] :
      ( k6_domain_1(A_31,'#skF_4'(A_31)) = A_31
      | ~ v1_zfmisc_1(A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2378,plain,(
    ! [A_197] :
      ( k1_tarski('#skF_4'(A_197)) = A_197
      | ~ v1_zfmisc_1(A_197)
      | v1_xboole_0(A_197)
      | ~ v1_zfmisc_1(A_197)
      | v1_xboole_0(A_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1654,c_40])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    ! [A_39,B_40] : k2_xboole_0(k1_tarski(A_39),B_40) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_67,plain,(
    ! [A_39] : k1_tarski(A_39) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_63])).

tff(c_34,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_3'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_331,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(k1_tarski(A_63),k1_tarski(B_64))
      | B_64 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( ~ r2_hidden(A_21,B_22)
      | ~ r1_xboole_0(k1_tarski(A_21),B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_350,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden(A_67,k1_tarski(B_68))
      | B_68 = A_67 ) ),
    inference(resolution,[status(thm)],[c_331,c_26])).

tff(c_358,plain,(
    ! [B_68] :
      ( '#skF_3'(k1_tarski(B_68)) = B_68
      | k1_tarski(B_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_350])).

tff(c_363,plain,(
    ! [B_69] : '#skF_3'(k1_tarski(B_69)) = B_69 ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_358])).

tff(c_372,plain,(
    ! [B_69] :
      ( r2_hidden(B_69,k1_tarski(B_69))
      | k1_tarski(B_69) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_34])).

tff(c_407,plain,(
    ! [B_73] : r2_hidden(B_73,k1_tarski(B_73)) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_372])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_416,plain,(
    ! [B_73] : ~ v1_xboole_0(k1_tarski(B_73)) ),
    inference(resolution,[status(thm)],[c_407,c_4])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_359,plain,(
    ! [B_68] :
      ( '#skF_1'(k1_tarski(B_68)) = B_68
      | v1_xboole_0(k1_tarski(B_68)) ) ),
    inference(resolution,[status(thm)],[c_6,c_350])).

tff(c_440,plain,(
    ! [B_68] : '#skF_1'(k1_tarski(B_68)) = B_68 ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_359])).

tff(c_3350,plain,(
    ! [A_241] :
      ( '#skF_4'(A_241) = '#skF_1'(A_241)
      | ~ v1_zfmisc_1(A_241)
      | v1_xboole_0(A_241)
      | ~ v1_zfmisc_1(A_241)
      | v1_xboole_0(A_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2378,c_440])).

tff(c_3352,plain,
    ( '#skF_4'('#skF_6') = '#skF_1'('#skF_6')
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_3350])).

tff(c_3355,plain,
    ( '#skF_4'('#skF_6') = '#skF_1'('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3352])).

tff(c_3356,plain,(
    '#skF_4'('#skF_6') = '#skF_1'('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3355])).

tff(c_1660,plain,(
    ! [A_161] :
      ( k1_tarski('#skF_4'(A_161)) = A_161
      | ~ v1_zfmisc_1(A_161)
      | v1_xboole_0(A_161)
      | ~ v1_zfmisc_1(A_161)
      | v1_xboole_0(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1654,c_40])).

tff(c_3360,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6')
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3356,c_1660])).

tff(c_3373,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_3360])).

tff(c_3374,plain,(
    k1_tarski('#skF_1'('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3373])).

tff(c_362,plain,(
    ! [B_68] : '#skF_3'(k1_tarski(B_68)) = B_68 ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_358])).

tff(c_3532,plain,(
    '#skF_1'('#skF_6') = '#skF_3'('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3374,c_362])).

tff(c_455,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_2'(A_80,B_81),A_80)
      | r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_338,plain,(
    ! [A_63,B_64] :
      ( ~ r2_hidden(A_63,k1_tarski(B_64))
      | B_64 = A_63 ) ),
    inference(resolution,[status(thm)],[c_331,c_26])).

tff(c_1012,plain,(
    ! [B_130,B_131] :
      ( '#skF_2'(k1_tarski(B_130),B_131) = B_130
      | r1_tarski(k1_tarski(B_130),B_131) ) ),
    inference(resolution,[status(thm)],[c_455,c_338])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1132,plain,(
    ! [B_137,B_138] :
      ( k2_xboole_0(k1_tarski(B_137),B_138) = B_138
      | '#skF_2'(k1_tarski(B_137),B_138) = B_137 ) ),
    inference(resolution,[status(thm)],[c_1012,c_14])).

tff(c_30,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1163,plain,(
    ! [B_138,B_137] :
      ( k1_xboole_0 != B_138
      | '#skF_2'(k1_tarski(B_137),B_138) = B_137 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_30])).

tff(c_3464,plain,(
    ! [B_138] :
      ( k1_xboole_0 != B_138
      | '#skF_2'('#skF_6',B_138) = '#skF_1'('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3374,c_1163])).

tff(c_4570,plain,(
    '#skF_3'('#skF_6') = '#skF_2'('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_3464])).

tff(c_4589,plain,(
    '#skF_1'('#skF_6') = '#skF_2'('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4570,c_3532])).

tff(c_1186,plain,(
    ! [A_1,B_137] :
      ( k2_xboole_0(A_1,k1_tarski(B_137)) = A_1
      | '#skF_2'(k1_tarski(B_137),A_1) = B_137 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1132])).

tff(c_3452,plain,(
    ! [A_1] :
      ( k2_xboole_0(A_1,'#skF_6') = A_1
      | '#skF_2'(k1_tarski('#skF_1'('#skF_6')),A_1) = '#skF_1'('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3374,c_1186])).

tff(c_3571,plain,(
    ! [A_1] :
      ( k2_xboole_0(A_1,'#skF_6') = A_1
      | '#skF_2'('#skF_6',A_1) = '#skF_1'('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3374,c_3452])).

tff(c_11176,plain,(
    ! [A_3134] :
      ( k2_xboole_0(A_3134,'#skF_6') = A_3134
      | '#skF_2'('#skF_6',k1_xboole_0) = '#skF_2'('#skF_6',A_3134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4589,c_3571])).

tff(c_11213,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_2'('#skF_6',k1_xboole_0) = '#skF_2'('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11176,c_205])).

tff(c_11291,plain,(
    '#skF_2'('#skF_6',k1_xboole_0) = '#skF_2'('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_11213])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_475,plain,(
    ! [A_84,B_85] :
      ( ~ r2_hidden('#skF_2'(A_84,B_85),B_85)
      | r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_480,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(resolution,[status(thm)],[c_12,c_475])).

tff(c_3680,plain,(
    k1_tarski('#skF_3'('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3532,c_3374])).

tff(c_463,plain,(
    ! [B_64,B_81] :
      ( '#skF_2'(k1_tarski(B_64),B_81) = B_64
      | r1_tarski(k1_tarski(B_64),B_81) ) ),
    inference(resolution,[status(thm)],[c_455,c_338])).

tff(c_555,plain,(
    ! [C_92,B_93,A_94] :
      ( r2_hidden(C_92,B_93)
      | ~ r2_hidden(C_92,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_942,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122),B_123)
      | ~ r1_tarski(A_122,B_123)
      | v1_xboole_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_6,c_555])).

tff(c_8,plain,(
    ! [C_11,B_8,A_7] :
      ( r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2128,plain,(
    ! [A_184,B_185,B_186] :
      ( r2_hidden('#skF_1'(A_184),B_185)
      | ~ r1_tarski(B_186,B_185)
      | ~ r1_tarski(A_184,B_186)
      | v1_xboole_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_942,c_8])).

tff(c_2147,plain,(
    ! [A_187] :
      ( r2_hidden('#skF_1'(A_187),'#skF_6')
      | ~ r1_tarski(A_187,'#skF_5')
      | v1_xboole_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_46,c_2128])).

tff(c_2158,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,'#skF_6')
      | ~ r1_tarski(k1_tarski(B_68),'#skF_5')
      | v1_xboole_0(k1_tarski(B_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_2147])).

tff(c_2163,plain,(
    ! [B_188] :
      ( r2_hidden(B_188,'#skF_6')
      | ~ r1_tarski(k1_tarski(B_188),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_2158])).

tff(c_2182,plain,(
    ! [B_189] :
      ( r2_hidden(B_189,'#skF_6')
      | '#skF_2'(k1_tarski(B_189),'#skF_5') = B_189 ) ),
    inference(resolution,[status(thm)],[c_463,c_2163])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2287,plain,(
    ! [B_195] :
      ( ~ r2_hidden(B_195,'#skF_5')
      | r1_tarski(k1_tarski(B_195),'#skF_5')
      | r2_hidden(B_195,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2182,c_10])).

tff(c_2162,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,'#skF_6')
      | ~ r1_tarski(k1_tarski(B_68),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_2158])).

tff(c_2338,plain,(
    ! [B_196] :
      ( ~ r2_hidden(B_196,'#skF_5')
      | r2_hidden(B_196,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2287,c_2162])).

tff(c_2366,plain,
    ( r2_hidden('#skF_3'('#skF_5'),'#skF_6')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_2338])).

tff(c_2377,plain,(
    r2_hidden('#skF_3'('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_2366])).

tff(c_2588,plain,(
    ! [B_200] :
      ( r2_hidden('#skF_3'('#skF_5'),B_200)
      | ~ r1_tarski('#skF_6',B_200) ) ),
    inference(resolution,[status(thm)],[c_2377,c_8])).

tff(c_2614,plain,(
    ! [B_64] :
      ( B_64 = '#skF_3'('#skF_5')
      | ~ r1_tarski('#skF_6',k1_tarski(B_64)) ) ),
    inference(resolution,[status(thm)],[c_2588,c_338])).

tff(c_3822,plain,
    ( '#skF_3'('#skF_5') = '#skF_3'('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3680,c_2614])).

tff(c_3970,plain,(
    '#skF_3'('#skF_5') = '#skF_3'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_3822])).

tff(c_4583,plain,(
    '#skF_3'('#skF_5') = '#skF_2'('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4570,c_3970])).

tff(c_11329,plain,(
    '#skF_3'('#skF_5') = '#skF_2'('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11291,c_4583])).

tff(c_12147,plain,
    ( r2_hidden('#skF_2'('#skF_6','#skF_5'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_11329,c_34])).

tff(c_12172,plain,(
    r2_hidden('#skF_2'('#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_12147])).

tff(c_12254,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_12172,c_10])).

tff(c_12309,plain,(
    k2_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12254,c_14])).

tff(c_12343,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_12309])).

tff(c_12345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_12343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:17:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.82/3.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.03  
% 9.11/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 9.11/3.04  
% 9.11/3.04  %Foreground sorts:
% 9.11/3.04  
% 9.11/3.04  
% 9.11/3.04  %Background operators:
% 9.11/3.04  
% 9.11/3.04  
% 9.11/3.04  %Foreground operators:
% 9.11/3.04  tff('#skF_4', type, '#skF_4': $i > $i).
% 9.11/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.11/3.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.11/3.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.11/3.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.11/3.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.11/3.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.11/3.04  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 9.11/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.11/3.04  tff('#skF_5', type, '#skF_5': $i).
% 9.11/3.04  tff('#skF_6', type, '#skF_6': $i).
% 9.11/3.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.11/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.11/3.04  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.11/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.11/3.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.11/3.04  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 9.11/3.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.11/3.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.11/3.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.11/3.04  
% 9.11/3.06  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 9.11/3.06  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.11/3.06  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.11/3.06  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 9.11/3.06  tff(f_60, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 9.11/3.06  tff(f_56, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 9.11/3.06  tff(f_100, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 9.11/3.06  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 9.11/3.06  tff(f_46, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 9.11/3.06  tff(f_73, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 9.11/3.06  tff(f_83, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 9.11/3.06  tff(f_70, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 9.11/3.06  tff(f_65, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 9.11/3.06  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.11/3.06  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.11/3.06  tff(c_44, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.11/3.06  tff(c_46, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.11/3.06  tff(c_201, plain, (![A_52, B_53]: (k2_xboole_0(A_52, B_53)=B_53 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.11/3.06  tff(c_205, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_201])).
% 9.11/3.06  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.11/3.06  tff(c_210, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_205, c_2])).
% 9.11/3.06  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.11/3.06  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.11/3.06  tff(c_216, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_205, c_18])).
% 9.11/3.06  tff(c_24, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.11/3.06  tff(c_390, plain, (![B_71, A_72]: (~r1_xboole_0(B_71, A_72) | ~r1_tarski(B_71, A_72) | v1_xboole_0(B_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.11/3.06  tff(c_580, plain, (![A_97, B_98]: (~r1_tarski(A_97, B_98) | v1_xboole_0(A_97) | k4_xboole_0(A_97, B_98)!=A_97)), inference(resolution, [status(thm)], [c_24, c_390])).
% 9.11/3.06  tff(c_589, plain, (v1_xboole_0('#skF_5') | k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(resolution, [status(thm)], [c_46, c_580])).
% 9.11/3.06  tff(c_594, plain, (v1_xboole_0('#skF_5') | k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_589])).
% 9.11/3.06  tff(c_595, plain, (k1_xboole_0!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_52, c_594])).
% 9.11/3.06  tff(c_50, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.11/3.06  tff(c_48, plain, (v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.11/3.06  tff(c_42, plain, (![A_31]: (m1_subset_1('#skF_4'(A_31), A_31) | ~v1_zfmisc_1(A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.11/3.06  tff(c_596, plain, (![A_99, B_100]: (k6_domain_1(A_99, B_100)=k1_tarski(B_100) | ~m1_subset_1(B_100, A_99) | v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.11/3.06  tff(c_1654, plain, (![A_161]: (k6_domain_1(A_161, '#skF_4'(A_161))=k1_tarski('#skF_4'(A_161)) | ~v1_zfmisc_1(A_161) | v1_xboole_0(A_161))), inference(resolution, [status(thm)], [c_42, c_596])).
% 9.11/3.06  tff(c_40, plain, (![A_31]: (k6_domain_1(A_31, '#skF_4'(A_31))=A_31 | ~v1_zfmisc_1(A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.11/3.06  tff(c_2378, plain, (![A_197]: (k1_tarski('#skF_4'(A_197))=A_197 | ~v1_zfmisc_1(A_197) | v1_xboole_0(A_197) | ~v1_zfmisc_1(A_197) | v1_xboole_0(A_197))), inference(superposition, [status(thm), theory('equality')], [c_1654, c_40])).
% 9.11/3.06  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.11/3.06  tff(c_63, plain, (![A_39, B_40]: (k2_xboole_0(k1_tarski(A_39), B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.11/3.06  tff(c_67, plain, (![A_39]: (k1_tarski(A_39)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_63])).
% 9.11/3.06  tff(c_34, plain, (![A_27]: (r2_hidden('#skF_3'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.11/3.06  tff(c_331, plain, (![A_63, B_64]: (r1_xboole_0(k1_tarski(A_63), k1_tarski(B_64)) | B_64=A_63)), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.11/3.06  tff(c_26, plain, (![A_21, B_22]: (~r2_hidden(A_21, B_22) | ~r1_xboole_0(k1_tarski(A_21), B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.11/3.06  tff(c_350, plain, (![A_67, B_68]: (~r2_hidden(A_67, k1_tarski(B_68)) | B_68=A_67)), inference(resolution, [status(thm)], [c_331, c_26])).
% 9.11/3.06  tff(c_358, plain, (![B_68]: ('#skF_3'(k1_tarski(B_68))=B_68 | k1_tarski(B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_350])).
% 9.11/3.06  tff(c_363, plain, (![B_69]: ('#skF_3'(k1_tarski(B_69))=B_69)), inference(negUnitSimplification, [status(thm)], [c_67, c_358])).
% 9.11/3.06  tff(c_372, plain, (![B_69]: (r2_hidden(B_69, k1_tarski(B_69)) | k1_tarski(B_69)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_363, c_34])).
% 9.11/3.06  tff(c_407, plain, (![B_73]: (r2_hidden(B_73, k1_tarski(B_73)))), inference(negUnitSimplification, [status(thm)], [c_67, c_372])).
% 9.11/3.06  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.11/3.06  tff(c_416, plain, (![B_73]: (~v1_xboole_0(k1_tarski(B_73)))), inference(resolution, [status(thm)], [c_407, c_4])).
% 9.11/3.06  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.11/3.06  tff(c_359, plain, (![B_68]: ('#skF_1'(k1_tarski(B_68))=B_68 | v1_xboole_0(k1_tarski(B_68)))), inference(resolution, [status(thm)], [c_6, c_350])).
% 9.11/3.06  tff(c_440, plain, (![B_68]: ('#skF_1'(k1_tarski(B_68))=B_68)), inference(negUnitSimplification, [status(thm)], [c_416, c_359])).
% 9.11/3.06  tff(c_3350, plain, (![A_241]: ('#skF_4'(A_241)='#skF_1'(A_241) | ~v1_zfmisc_1(A_241) | v1_xboole_0(A_241) | ~v1_zfmisc_1(A_241) | v1_xboole_0(A_241))), inference(superposition, [status(thm), theory('equality')], [c_2378, c_440])).
% 9.11/3.06  tff(c_3352, plain, ('#skF_4'('#skF_6')='#skF_1'('#skF_6') | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_48, c_3350])).
% 9.11/3.06  tff(c_3355, plain, ('#skF_4'('#skF_6')='#skF_1'('#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3352])).
% 9.11/3.06  tff(c_3356, plain, ('#skF_4'('#skF_6')='#skF_1'('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_3355])).
% 9.11/3.06  tff(c_1660, plain, (![A_161]: (k1_tarski('#skF_4'(A_161))=A_161 | ~v1_zfmisc_1(A_161) | v1_xboole_0(A_161) | ~v1_zfmisc_1(A_161) | v1_xboole_0(A_161))), inference(superposition, [status(thm), theory('equality')], [c_1654, c_40])).
% 9.11/3.06  tff(c_3360, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6') | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3356, c_1660])).
% 9.11/3.06  tff(c_3373, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_3360])).
% 9.11/3.06  tff(c_3374, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_50, c_3373])).
% 9.11/3.06  tff(c_362, plain, (![B_68]: ('#skF_3'(k1_tarski(B_68))=B_68)), inference(negUnitSimplification, [status(thm)], [c_67, c_358])).
% 9.11/3.06  tff(c_3532, plain, ('#skF_1'('#skF_6')='#skF_3'('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3374, c_362])).
% 9.11/3.06  tff(c_455, plain, (![A_80, B_81]: (r2_hidden('#skF_2'(A_80, B_81), A_80) | r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.11/3.06  tff(c_338, plain, (![A_63, B_64]: (~r2_hidden(A_63, k1_tarski(B_64)) | B_64=A_63)), inference(resolution, [status(thm)], [c_331, c_26])).
% 9.11/3.06  tff(c_1012, plain, (![B_130, B_131]: ('#skF_2'(k1_tarski(B_130), B_131)=B_130 | r1_tarski(k1_tarski(B_130), B_131))), inference(resolution, [status(thm)], [c_455, c_338])).
% 9.11/3.06  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.11/3.06  tff(c_1132, plain, (![B_137, B_138]: (k2_xboole_0(k1_tarski(B_137), B_138)=B_138 | '#skF_2'(k1_tarski(B_137), B_138)=B_137)), inference(resolution, [status(thm)], [c_1012, c_14])).
% 9.11/3.06  tff(c_30, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.11/3.06  tff(c_1163, plain, (![B_138, B_137]: (k1_xboole_0!=B_138 | '#skF_2'(k1_tarski(B_137), B_138)=B_137)), inference(superposition, [status(thm), theory('equality')], [c_1132, c_30])).
% 9.11/3.06  tff(c_3464, plain, (![B_138]: (k1_xboole_0!=B_138 | '#skF_2'('#skF_6', B_138)='#skF_1'('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3374, c_1163])).
% 9.11/3.06  tff(c_4570, plain, ('#skF_3'('#skF_6')='#skF_2'('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_3464])).
% 9.11/3.06  tff(c_4589, plain, ('#skF_1'('#skF_6')='#skF_2'('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4570, c_3532])).
% 9.11/3.06  tff(c_1186, plain, (![A_1, B_137]: (k2_xboole_0(A_1, k1_tarski(B_137))=A_1 | '#skF_2'(k1_tarski(B_137), A_1)=B_137)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1132])).
% 9.11/3.06  tff(c_3452, plain, (![A_1]: (k2_xboole_0(A_1, '#skF_6')=A_1 | '#skF_2'(k1_tarski('#skF_1'('#skF_6')), A_1)='#skF_1'('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3374, c_1186])).
% 9.11/3.06  tff(c_3571, plain, (![A_1]: (k2_xboole_0(A_1, '#skF_6')=A_1 | '#skF_2'('#skF_6', A_1)='#skF_1'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3374, c_3452])).
% 9.11/3.06  tff(c_11176, plain, (![A_3134]: (k2_xboole_0(A_3134, '#skF_6')=A_3134 | '#skF_2'('#skF_6', k1_xboole_0)='#skF_2'('#skF_6', A_3134))), inference(demodulation, [status(thm), theory('equality')], [c_4589, c_3571])).
% 9.11/3.06  tff(c_11213, plain, ('#skF_5'='#skF_6' | '#skF_2'('#skF_6', k1_xboole_0)='#skF_2'('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11176, c_205])).
% 9.11/3.06  tff(c_11291, plain, ('#skF_2'('#skF_6', k1_xboole_0)='#skF_2'('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_11213])).
% 9.11/3.06  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.11/3.06  tff(c_475, plain, (![A_84, B_85]: (~r2_hidden('#skF_2'(A_84, B_85), B_85) | r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.11/3.06  tff(c_480, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(resolution, [status(thm)], [c_12, c_475])).
% 9.11/3.06  tff(c_3680, plain, (k1_tarski('#skF_3'('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3532, c_3374])).
% 9.11/3.06  tff(c_463, plain, (![B_64, B_81]: ('#skF_2'(k1_tarski(B_64), B_81)=B_64 | r1_tarski(k1_tarski(B_64), B_81))), inference(resolution, [status(thm)], [c_455, c_338])).
% 9.11/3.06  tff(c_555, plain, (![C_92, B_93, A_94]: (r2_hidden(C_92, B_93) | ~r2_hidden(C_92, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.11/3.06  tff(c_942, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122), B_123) | ~r1_tarski(A_122, B_123) | v1_xboole_0(A_122))), inference(resolution, [status(thm)], [c_6, c_555])).
% 9.11/3.06  tff(c_8, plain, (![C_11, B_8, A_7]: (r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.11/3.06  tff(c_2128, plain, (![A_184, B_185, B_186]: (r2_hidden('#skF_1'(A_184), B_185) | ~r1_tarski(B_186, B_185) | ~r1_tarski(A_184, B_186) | v1_xboole_0(A_184))), inference(resolution, [status(thm)], [c_942, c_8])).
% 9.11/3.06  tff(c_2147, plain, (![A_187]: (r2_hidden('#skF_1'(A_187), '#skF_6') | ~r1_tarski(A_187, '#skF_5') | v1_xboole_0(A_187))), inference(resolution, [status(thm)], [c_46, c_2128])).
% 9.11/3.06  tff(c_2158, plain, (![B_68]: (r2_hidden(B_68, '#skF_6') | ~r1_tarski(k1_tarski(B_68), '#skF_5') | v1_xboole_0(k1_tarski(B_68)))), inference(superposition, [status(thm), theory('equality')], [c_440, c_2147])).
% 9.11/3.06  tff(c_2163, plain, (![B_188]: (r2_hidden(B_188, '#skF_6') | ~r1_tarski(k1_tarski(B_188), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_416, c_2158])).
% 9.11/3.06  tff(c_2182, plain, (![B_189]: (r2_hidden(B_189, '#skF_6') | '#skF_2'(k1_tarski(B_189), '#skF_5')=B_189)), inference(resolution, [status(thm)], [c_463, c_2163])).
% 9.11/3.06  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.11/3.06  tff(c_2287, plain, (![B_195]: (~r2_hidden(B_195, '#skF_5') | r1_tarski(k1_tarski(B_195), '#skF_5') | r2_hidden(B_195, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2182, c_10])).
% 9.11/3.06  tff(c_2162, plain, (![B_68]: (r2_hidden(B_68, '#skF_6') | ~r1_tarski(k1_tarski(B_68), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_416, c_2158])).
% 9.11/3.06  tff(c_2338, plain, (![B_196]: (~r2_hidden(B_196, '#skF_5') | r2_hidden(B_196, '#skF_6'))), inference(resolution, [status(thm)], [c_2287, c_2162])).
% 9.11/3.06  tff(c_2366, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_6') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_34, c_2338])).
% 9.11/3.06  tff(c_2377, plain, (r2_hidden('#skF_3'('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_595, c_2366])).
% 9.11/3.06  tff(c_2588, plain, (![B_200]: (r2_hidden('#skF_3'('#skF_5'), B_200) | ~r1_tarski('#skF_6', B_200))), inference(resolution, [status(thm)], [c_2377, c_8])).
% 9.11/3.06  tff(c_2614, plain, (![B_64]: (B_64='#skF_3'('#skF_5') | ~r1_tarski('#skF_6', k1_tarski(B_64)))), inference(resolution, [status(thm)], [c_2588, c_338])).
% 9.11/3.06  tff(c_3822, plain, ('#skF_3'('#skF_5')='#skF_3'('#skF_6') | ~r1_tarski('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3680, c_2614])).
% 9.11/3.06  tff(c_3970, plain, ('#skF_3'('#skF_5')='#skF_3'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_3822])).
% 9.11/3.06  tff(c_4583, plain, ('#skF_3'('#skF_5')='#skF_2'('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4570, c_3970])).
% 9.11/3.06  tff(c_11329, plain, ('#skF_3'('#skF_5')='#skF_2'('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11291, c_4583])).
% 9.11/3.06  tff(c_12147, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5'), '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_11329, c_34])).
% 9.11/3.06  tff(c_12172, plain, (r2_hidden('#skF_2'('#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_595, c_12147])).
% 9.11/3.06  tff(c_12254, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_12172, c_10])).
% 9.11/3.06  tff(c_12309, plain, (k2_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_12254, c_14])).
% 9.11/3.06  tff(c_12343, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_210, c_12309])).
% 9.11/3.06  tff(c_12345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_12343])).
% 9.11/3.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.06  
% 9.11/3.06  Inference rules
% 9.11/3.06  ----------------------
% 9.11/3.06  #Ref     : 1
% 9.11/3.06  #Sup     : 2619
% 9.11/3.06  #Fact    : 0
% 9.11/3.06  #Define  : 0
% 9.11/3.06  #Split   : 3
% 9.11/3.06  #Chain   : 0
% 9.11/3.06  #Close   : 0
% 9.11/3.06  
% 9.11/3.06  Ordering : KBO
% 9.11/3.06  
% 9.11/3.06  Simplification rules
% 9.11/3.06  ----------------------
% 9.11/3.06  #Subsume      : 1025
% 9.11/3.06  #Demod        : 887
% 9.11/3.06  #Tautology    : 582
% 9.11/3.06  #SimpNegUnit  : 504
% 9.11/3.06  #BackRed      : 71
% 9.11/3.06  
% 9.11/3.06  #Partial instantiations: 2728
% 9.11/3.06  #Strategies tried      : 1
% 9.11/3.06  
% 9.11/3.06  Timing (in seconds)
% 9.11/3.06  ----------------------
% 9.11/3.06  Preprocessing        : 0.31
% 9.11/3.06  Parsing              : 0.17
% 9.11/3.06  CNF conversion       : 0.02
% 9.11/3.06  Main loop            : 1.96
% 9.11/3.06  Inferencing          : 0.64
% 9.11/3.06  Reduction            : 0.67
% 9.11/3.06  Demodulation         : 0.43
% 9.11/3.06  BG Simplification    : 0.06
% 9.11/3.06  Subsumption          : 0.47
% 9.11/3.06  Abstraction          : 0.08
% 9.11/3.06  MUC search           : 0.00
% 9.11/3.06  Cooper               : 0.00
% 9.11/3.06  Total                : 2.32
% 9.11/3.06  Index Insertion      : 0.00
% 9.11/3.06  Index Deletion       : 0.00
% 9.11/3.06  Index Matching       : 0.00
% 9.11/3.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
