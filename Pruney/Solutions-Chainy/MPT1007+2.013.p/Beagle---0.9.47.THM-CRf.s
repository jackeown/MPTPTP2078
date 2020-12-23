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
% DateTime   : Thu Dec  3 10:14:12 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 337 expanded)
%              Number of leaves         :   44 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          :  208 ( 834 expanded)
%              Number of equality atoms :   61 ( 234 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_123,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_37,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_58,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_235,plain,(
    ! [C_103,A_104,B_105] :
      ( r2_hidden(C_103,A_104)
      | ~ r2_hidden(C_103,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_797,plain,(
    ! [A_154,A_155,B_156] :
      ( r2_hidden(A_154,A_155)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155))
      | v1_xboole_0(B_156)
      | ~ m1_subset_1(A_154,B_156) ) ),
    inference(resolution,[status(thm)],[c_20,c_235])).

tff(c_809,plain,(
    ! [A_154] :
      ( r2_hidden(A_154,k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_154,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_797])).

tff(c_813,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_809])).

tff(c_50,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_2'(A_38),A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_242,plain,(
    ! [A_106,A_107] :
      ( r2_hidden('#skF_2'(A_106),A_107)
      | ~ m1_subset_1(A_106,k1_zfmisc_1(A_107))
      | k1_xboole_0 = A_106 ) ),
    inference(resolution,[status(thm)],[c_50,c_235])).

tff(c_48,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_mcart_1(A_35) = B_36
      | ~ r2_hidden(A_35,k2_zfmisc_1(k1_tarski(B_36),C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1226,plain,(
    ! [A_185,B_186,C_187] :
      ( k1_mcart_1('#skF_2'(A_185)) = B_186
      | ~ m1_subset_1(A_185,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_186),C_187)))
      | k1_xboole_0 = A_185 ) ),
    inference(resolution,[status(thm)],[c_242,c_48])).

tff(c_1251,plain,
    ( k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_62,c_1226])).

tff(c_1255,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1251])).

tff(c_1292,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_60])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_18,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_115,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_129,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_115])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_79,plain,(
    ! [A_56] :
      ( v1_funct_1(A_56)
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_83,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_321,plain,(
    ! [A_112,B_113] :
      ( k1_funct_1(A_112,B_113) = k1_xboole_0
      | r2_hidden(B_113,k1_relat_1(A_112))
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_333,plain,(
    ! [B_113] :
      ( k1_funct_1(k1_xboole_0,B_113) = k1_xboole_0
      | r2_hidden(B_113,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_321])).

tff(c_355,plain,(
    ! [B_114] :
      ( k1_funct_1(k1_xboole_0,B_114) = k1_xboole_0
      | r2_hidden(B_114,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_83,c_333])).

tff(c_38,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_366,plain,(
    ! [B_114] :
      ( ~ r1_tarski(k1_xboole_0,B_114)
      | k1_funct_1(k1_xboole_0,B_114) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_355,c_38])).

tff(c_377,plain,(
    ! [B_114] : k1_funct_1(k1_xboole_0,B_114) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_366])).

tff(c_1274,plain,(
    ! [B_114] : k1_funct_1('#skF_5',B_114) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_1255,c_377])).

tff(c_1382,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_58])).

tff(c_1287,plain,(
    ! [A_15] : m1_subset_1('#skF_5',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_18])).

tff(c_536,plain,(
    ! [D_127,C_128,B_129,A_130] :
      ( r2_hidden(k1_funct_1(D_127,C_128),B_129)
      | k1_xboole_0 = B_129
      | ~ r2_hidden(C_128,A_130)
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ v1_funct_2(D_127,A_130,B_129)
      | ~ v1_funct_1(D_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_551,plain,(
    ! [D_127,A_38,B_129] :
      ( r2_hidden(k1_funct_1(D_127,'#skF_2'(A_38)),B_129)
      | k1_xboole_0 = B_129
      | ~ m1_subset_1(D_127,k1_zfmisc_1(k2_zfmisc_1(A_38,B_129)))
      | ~ v1_funct_2(D_127,A_38,B_129)
      | ~ v1_funct_1(D_127)
      | k1_xboole_0 = A_38 ) ),
    inference(resolution,[status(thm)],[c_50,c_536])).

tff(c_2455,plain,(
    ! [D_290,A_291,B_292] :
      ( r2_hidden(k1_funct_1(D_290,'#skF_2'(A_291)),B_292)
      | B_292 = '#skF_5'
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_2(D_290,A_291,B_292)
      | ~ v1_funct_1(D_290)
      | A_291 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_1255,c_551])).

tff(c_2493,plain,(
    ! [B_292,A_291] :
      ( r2_hidden('#skF_5',B_292)
      | B_292 = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_2('#skF_5',A_291,B_292)
      | ~ v1_funct_1('#skF_5')
      | A_291 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1274,c_2455])).

tff(c_2509,plain,(
    ! [B_293,A_294] :
      ( r2_hidden('#skF_5',B_293)
      | B_293 = '#skF_5'
      | ~ v1_funct_2('#skF_5',A_294,B_293)
      | A_294 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1287,c_2493])).

tff(c_2512,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_tarski('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_64,c_2509])).

tff(c_2515,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1292,c_1382,c_2512])).

tff(c_12,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2538,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2515,c_12])).

tff(c_2548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_2538])).

tff(c_2550,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1251])).

tff(c_2549,plain,(
    k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1251])).

tff(c_44,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden(k1_mcart_1(A_32),B_33)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2555,plain,(
    ! [A_295,B_296,C_297] :
      ( r2_hidden(k1_mcart_1('#skF_2'(A_295)),B_296)
      | ~ m1_subset_1(A_295,k1_zfmisc_1(k2_zfmisc_1(B_296,C_297)))
      | k1_xboole_0 = A_295 ) ),
    inference(resolution,[status(thm)],[c_242,c_44])).

tff(c_2567,plain,
    ( r2_hidden(k1_mcart_1('#skF_2'('#skF_5')),k1_tarski('#skF_3'))
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_62,c_2555])).

tff(c_2578,plain,
    ( r2_hidden('#skF_3',k1_tarski('#skF_3'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_2567])).

tff(c_2579,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2550,c_2578])).

tff(c_56,plain,(
    ! [D_51,C_50,B_49,A_48] :
      ( r2_hidden(k1_funct_1(D_51,C_50),B_49)
      | k1_xboole_0 = B_49
      | ~ r2_hidden(C_50,A_48)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(D_51,A_48,B_49)
      | ~ v1_funct_1(D_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2617,plain,(
    ! [D_303,B_304] :
      ( r2_hidden(k1_funct_1(D_303,'#skF_3'),B_304)
      | k1_xboole_0 = B_304
      | ~ m1_subset_1(D_303,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),B_304)))
      | ~ v1_funct_2(D_303,k1_tarski('#skF_3'),B_304)
      | ~ v1_funct_1(D_303) ) ),
    inference(resolution,[status(thm)],[c_2579,c_56])).

tff(c_2632,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2617])).

tff(c_2647,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2632])).

tff(c_2649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_2647])).

tff(c_2651,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_809])).

tff(c_3304,plain,(
    ! [A_360,B_361,C_362] :
      ( r2_hidden(k1_mcart_1('#skF_2'(A_360)),B_361)
      | ~ m1_subset_1(A_360,k1_zfmisc_1(k2_zfmisc_1(B_361,C_362)))
      | k1_xboole_0 = A_360 ) ),
    inference(resolution,[status(thm)],[c_242,c_44])).

tff(c_3326,plain,
    ( r2_hidden(k1_mcart_1('#skF_2'('#skF_5')),k1_tarski('#skF_3'))
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_62,c_3304])).

tff(c_3330,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3326])).

tff(c_3369,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3330,c_2])).

tff(c_3374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2651,c_3369])).

tff(c_3376,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3326])).

tff(c_3458,plain,(
    ! [A_371,B_372,C_373] :
      ( k1_mcart_1('#skF_2'(A_371)) = B_372
      | ~ m1_subset_1(A_371,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_372),C_373)))
      | k1_xboole_0 = A_371 ) ),
    inference(resolution,[status(thm)],[c_242,c_48])).

tff(c_3472,plain,
    ( k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_62,c_3458])).

tff(c_3485,plain,(
    k1_mcart_1('#skF_2'('#skF_5')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3376,c_3472])).

tff(c_3375,plain,(
    r2_hidden(k1_mcart_1('#skF_2'('#skF_5')),k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3326])).

tff(c_3388,plain,(
    ! [D_51,B_49] :
      ( r2_hidden(k1_funct_1(D_51,k1_mcart_1('#skF_2'('#skF_5'))),B_49)
      | k1_xboole_0 = B_49
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),B_49)))
      | ~ v1_funct_2(D_51,k1_tarski('#skF_3'),B_49)
      | ~ v1_funct_1(D_51) ) ),
    inference(resolution,[status(thm)],[c_3375,c_56])).

tff(c_4078,plain,(
    ! [D_440,B_441] :
      ( r2_hidden(k1_funct_1(D_440,'#skF_3'),B_441)
      | k1_xboole_0 = B_441
      | ~ m1_subset_1(D_440,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),B_441)))
      | ~ v1_funct_2(D_440,k1_tarski('#skF_3'),B_441)
      | ~ v1_funct_1(D_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3485,c_3388])).

tff(c_4093,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_4078])).

tff(c_4108,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4093])).

tff(c_4110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_4108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:39:20 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.05  
% 5.35/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.05  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 5.35/2.05  
% 5.35/2.05  %Foreground sorts:
% 5.35/2.05  
% 5.35/2.05  
% 5.35/2.05  %Background operators:
% 5.35/2.05  
% 5.35/2.05  
% 5.35/2.05  %Foreground operators:
% 5.35/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.35/2.05  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.35/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.35/2.05  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.35/2.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.35/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.35/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/2.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.35/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.35/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.35/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.35/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.35/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.35/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.35/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/2.05  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.35/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.05  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.35/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.35/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.35/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.35/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.05  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.35/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.35/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.35/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/2.05  
% 5.35/2.07  tff(f_147, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 5.35/2.07  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.35/2.07  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.35/2.07  tff(f_123, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 5.35/2.07  tff(f_107, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 5.35/2.07  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.35/2.07  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.35/2.07  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.35/2.07  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.35/2.07  tff(f_68, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 5.35/2.07  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.35/2.07  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 5.35/2.07  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.35/2.07  tff(f_135, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.35/2.07  tff(f_37, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.35/2.07  tff(f_101, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 5.35/2.07  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.35/2.07  tff(c_58, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.35/2.07  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.35/2.07  tff(c_64, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.35/2.07  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.35/2.07  tff(c_20, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.35/2.07  tff(c_235, plain, (![C_103, A_104, B_105]: (r2_hidden(C_103, A_104) | ~r2_hidden(C_103, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.35/2.07  tff(c_797, plain, (![A_154, A_155, B_156]: (r2_hidden(A_154, A_155) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)) | v1_xboole_0(B_156) | ~m1_subset_1(A_154, B_156))), inference(resolution, [status(thm)], [c_20, c_235])).
% 5.35/2.07  tff(c_809, plain, (![A_154]: (r2_hidden(A_154, k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')) | v1_xboole_0('#skF_5') | ~m1_subset_1(A_154, '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_797])).
% 5.35/2.07  tff(c_813, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_809])).
% 5.35/2.07  tff(c_50, plain, (![A_38]: (r2_hidden('#skF_2'(A_38), A_38) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.35/2.07  tff(c_242, plain, (![A_106, A_107]: (r2_hidden('#skF_2'(A_106), A_107) | ~m1_subset_1(A_106, k1_zfmisc_1(A_107)) | k1_xboole_0=A_106)), inference(resolution, [status(thm)], [c_50, c_235])).
% 5.35/2.07  tff(c_48, plain, (![A_35, B_36, C_37]: (k1_mcart_1(A_35)=B_36 | ~r2_hidden(A_35, k2_zfmisc_1(k1_tarski(B_36), C_37)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.35/2.07  tff(c_1226, plain, (![A_185, B_186, C_187]: (k1_mcart_1('#skF_2'(A_185))=B_186 | ~m1_subset_1(A_185, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_186), C_187))) | k1_xboole_0=A_185)), inference(resolution, [status(thm)], [c_242, c_48])).
% 5.35/2.07  tff(c_1251, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_62, c_1226])).
% 5.35/2.07  tff(c_1255, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1251])).
% 5.35/2.07  tff(c_1292, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_60])).
% 5.35/2.07  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.35/2.07  tff(c_18, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.35/2.07  tff(c_115, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.35/2.07  tff(c_129, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_115])).
% 5.35/2.07  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.35/2.07  tff(c_79, plain, (![A_56]: (v1_funct_1(A_56) | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.35/2.07  tff(c_83, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_79])).
% 5.35/2.07  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.35/2.07  tff(c_321, plain, (![A_112, B_113]: (k1_funct_1(A_112, B_113)=k1_xboole_0 | r2_hidden(B_113, k1_relat_1(A_112)) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.35/2.07  tff(c_333, plain, (![B_113]: (k1_funct_1(k1_xboole_0, B_113)=k1_xboole_0 | r2_hidden(B_113, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_321])).
% 5.35/2.07  tff(c_355, plain, (![B_114]: (k1_funct_1(k1_xboole_0, B_114)=k1_xboole_0 | r2_hidden(B_114, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_83, c_333])).
% 5.35/2.07  tff(c_38, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.35/2.07  tff(c_366, plain, (![B_114]: (~r1_tarski(k1_xboole_0, B_114) | k1_funct_1(k1_xboole_0, B_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_355, c_38])).
% 5.35/2.07  tff(c_377, plain, (![B_114]: (k1_funct_1(k1_xboole_0, B_114)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_366])).
% 5.35/2.07  tff(c_1274, plain, (![B_114]: (k1_funct_1('#skF_5', B_114)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_1255, c_377])).
% 5.35/2.07  tff(c_1382, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_58])).
% 5.35/2.07  tff(c_1287, plain, (![A_15]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_18])).
% 5.35/2.07  tff(c_536, plain, (![D_127, C_128, B_129, A_130]: (r2_hidden(k1_funct_1(D_127, C_128), B_129) | k1_xboole_0=B_129 | ~r2_hidden(C_128, A_130) | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_2(D_127, A_130, B_129) | ~v1_funct_1(D_127))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.35/2.07  tff(c_551, plain, (![D_127, A_38, B_129]: (r2_hidden(k1_funct_1(D_127, '#skF_2'(A_38)), B_129) | k1_xboole_0=B_129 | ~m1_subset_1(D_127, k1_zfmisc_1(k2_zfmisc_1(A_38, B_129))) | ~v1_funct_2(D_127, A_38, B_129) | ~v1_funct_1(D_127) | k1_xboole_0=A_38)), inference(resolution, [status(thm)], [c_50, c_536])).
% 5.35/2.07  tff(c_2455, plain, (![D_290, A_291, B_292]: (r2_hidden(k1_funct_1(D_290, '#skF_2'(A_291)), B_292) | B_292='#skF_5' | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_2(D_290, A_291, B_292) | ~v1_funct_1(D_290) | A_291='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_1255, c_551])).
% 5.35/2.07  tff(c_2493, plain, (![B_292, A_291]: (r2_hidden('#skF_5', B_292) | B_292='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_2('#skF_5', A_291, B_292) | ~v1_funct_1('#skF_5') | A_291='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1274, c_2455])).
% 5.35/2.07  tff(c_2509, plain, (![B_293, A_294]: (r2_hidden('#skF_5', B_293) | B_293='#skF_5' | ~v1_funct_2('#skF_5', A_294, B_293) | A_294='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1287, c_2493])).
% 5.35/2.07  tff(c_2512, plain, (r2_hidden('#skF_5', '#skF_4') | '#skF_5'='#skF_4' | k1_tarski('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_64, c_2509])).
% 5.35/2.07  tff(c_2515, plain, (k1_tarski('#skF_3')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1292, c_1382, c_2512])).
% 5.35/2.07  tff(c_12, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.35/2.07  tff(c_2538, plain, (~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2515, c_12])).
% 5.35/2.07  tff(c_2548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_813, c_2538])).
% 5.35/2.07  tff(c_2550, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_1251])).
% 5.35/2.07  tff(c_2549, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3'), inference(splitRight, [status(thm)], [c_1251])).
% 5.35/2.07  tff(c_44, plain, (![A_32, B_33, C_34]: (r2_hidden(k1_mcart_1(A_32), B_33) | ~r2_hidden(A_32, k2_zfmisc_1(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.35/2.07  tff(c_2555, plain, (![A_295, B_296, C_297]: (r2_hidden(k1_mcart_1('#skF_2'(A_295)), B_296) | ~m1_subset_1(A_295, k1_zfmisc_1(k2_zfmisc_1(B_296, C_297))) | k1_xboole_0=A_295)), inference(resolution, [status(thm)], [c_242, c_44])).
% 5.35/2.07  tff(c_2567, plain, (r2_hidden(k1_mcart_1('#skF_2'('#skF_5')), k1_tarski('#skF_3')) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_62, c_2555])).
% 5.35/2.07  tff(c_2578, plain, (r2_hidden('#skF_3', k1_tarski('#skF_3')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_2567])).
% 5.35/2.07  tff(c_2579, plain, (r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2550, c_2578])).
% 5.35/2.07  tff(c_56, plain, (![D_51, C_50, B_49, A_48]: (r2_hidden(k1_funct_1(D_51, C_50), B_49) | k1_xboole_0=B_49 | ~r2_hidden(C_50, A_48) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(D_51, A_48, B_49) | ~v1_funct_1(D_51))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.35/2.07  tff(c_2617, plain, (![D_303, B_304]: (r2_hidden(k1_funct_1(D_303, '#skF_3'), B_304) | k1_xboole_0=B_304 | ~m1_subset_1(D_303, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), B_304))) | ~v1_funct_2(D_303, k1_tarski('#skF_3'), B_304) | ~v1_funct_1(D_303))), inference(resolution, [status(thm)], [c_2579, c_56])).
% 5.35/2.07  tff(c_2632, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_2617])).
% 5.35/2.07  tff(c_2647, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2632])).
% 5.35/2.07  tff(c_2649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_2647])).
% 5.35/2.07  tff(c_2651, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_809])).
% 5.35/2.07  tff(c_3304, plain, (![A_360, B_361, C_362]: (r2_hidden(k1_mcart_1('#skF_2'(A_360)), B_361) | ~m1_subset_1(A_360, k1_zfmisc_1(k2_zfmisc_1(B_361, C_362))) | k1_xboole_0=A_360)), inference(resolution, [status(thm)], [c_242, c_44])).
% 5.35/2.07  tff(c_3326, plain, (r2_hidden(k1_mcart_1('#skF_2'('#skF_5')), k1_tarski('#skF_3')) | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_62, c_3304])).
% 5.35/2.07  tff(c_3330, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3326])).
% 5.35/2.07  tff(c_3369, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3330, c_2])).
% 5.35/2.07  tff(c_3374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2651, c_3369])).
% 5.35/2.07  tff(c_3376, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_3326])).
% 5.35/2.07  tff(c_3458, plain, (![A_371, B_372, C_373]: (k1_mcart_1('#skF_2'(A_371))=B_372 | ~m1_subset_1(A_371, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_372), C_373))) | k1_xboole_0=A_371)), inference(resolution, [status(thm)], [c_242, c_48])).
% 5.35/2.07  tff(c_3472, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_62, c_3458])).
% 5.35/2.07  tff(c_3485, plain, (k1_mcart_1('#skF_2'('#skF_5'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3376, c_3472])).
% 5.35/2.07  tff(c_3375, plain, (r2_hidden(k1_mcart_1('#skF_2'('#skF_5')), k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_3326])).
% 5.35/2.07  tff(c_3388, plain, (![D_51, B_49]: (r2_hidden(k1_funct_1(D_51, k1_mcart_1('#skF_2'('#skF_5'))), B_49) | k1_xboole_0=B_49 | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), B_49))) | ~v1_funct_2(D_51, k1_tarski('#skF_3'), B_49) | ~v1_funct_1(D_51))), inference(resolution, [status(thm)], [c_3375, c_56])).
% 5.35/2.07  tff(c_4078, plain, (![D_440, B_441]: (r2_hidden(k1_funct_1(D_440, '#skF_3'), B_441) | k1_xboole_0=B_441 | ~m1_subset_1(D_440, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), B_441))) | ~v1_funct_2(D_440, k1_tarski('#skF_3'), B_441) | ~v1_funct_1(D_440))), inference(demodulation, [status(thm), theory('equality')], [c_3485, c_3388])).
% 5.35/2.07  tff(c_4093, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_4078])).
% 5.35/2.07  tff(c_4108, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_4093])).
% 5.35/2.07  tff(c_4110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_4108])).
% 5.35/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.07  
% 5.35/2.07  Inference rules
% 5.35/2.07  ----------------------
% 5.35/2.07  #Ref     : 0
% 5.35/2.07  #Sup     : 889
% 5.35/2.07  #Fact    : 0
% 5.35/2.07  #Define  : 0
% 5.35/2.07  #Split   : 22
% 5.35/2.07  #Chain   : 0
% 5.35/2.07  #Close   : 0
% 5.35/2.07  
% 5.35/2.07  Ordering : KBO
% 5.35/2.07  
% 5.35/2.07  Simplification rules
% 5.35/2.07  ----------------------
% 5.35/2.07  #Subsume      : 145
% 5.35/2.07  #Demod        : 757
% 5.35/2.07  #Tautology    : 317
% 5.35/2.07  #SimpNegUnit  : 52
% 5.35/2.07  #BackRed      : 93
% 5.35/2.07  
% 5.35/2.07  #Partial instantiations: 0
% 5.35/2.07  #Strategies tried      : 1
% 5.35/2.07  
% 5.35/2.07  Timing (in seconds)
% 5.35/2.07  ----------------------
% 5.35/2.07  Preprocessing        : 0.34
% 5.35/2.07  Parsing              : 0.18
% 5.35/2.07  CNF conversion       : 0.02
% 5.35/2.07  Main loop            : 0.96
% 5.35/2.07  Inferencing          : 0.33
% 5.35/2.07  Reduction            : 0.32
% 5.35/2.07  Demodulation         : 0.21
% 5.35/2.07  BG Simplification    : 0.04
% 5.35/2.07  Subsumption          : 0.18
% 5.35/2.07  Abstraction          : 0.05
% 5.35/2.07  MUC search           : 0.00
% 5.35/2.07  Cooper               : 0.00
% 5.35/2.07  Total                : 1.35
% 5.35/2.07  Index Insertion      : 0.00
% 5.35/2.07  Index Deletion       : 0.00
% 5.35/2.07  Index Matching       : 0.00
% 5.35/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
