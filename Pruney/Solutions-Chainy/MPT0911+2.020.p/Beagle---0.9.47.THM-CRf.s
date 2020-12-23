%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:04 EST 2020

% Result     : Theorem 15.20s
% Output     : CNFRefutation 15.35s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 344 expanded)
%              Number of leaves         :   39 ( 136 expanded)
%              Depth                    :   14
%              Number of atoms          :  195 ( 982 expanded)
%              Number of equality atoms :   92 ( 465 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_86,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_496,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k7_mcart_1(A_178,B_179,C_180,D_181) = k2_mcart_1(D_181)
      | ~ m1_subset_1(D_181,k3_zfmisc_1(A_178,B_179,C_180))
      | k1_xboole_0 = C_180
      | k1_xboole_0 = B_179
      | k1_xboole_0 = A_178 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_507,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_496])).

tff(c_512,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_507])).

tff(c_54,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_513,plain,(
    k2_mcart_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_54])).

tff(c_197,plain,(
    ! [A_110,B_111,C_112] : k2_zfmisc_1(k2_zfmisc_1(A_110,B_111),C_112) = k3_zfmisc_1(A_110,B_111,C_112) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_205,plain,(
    ! [A_110,B_111,C_112] : v1_relat_1(k3_zfmisc_1(A_110,B_111,C_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_10])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_332,plain,(
    ! [A_149,B_150] :
      ( k4_tarski(k1_mcart_1(A_149),k2_mcart_1(A_149)) = A_149
      | ~ r2_hidden(A_149,B_150)
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7886,plain,(
    ! [A_495,B_496] :
      ( k4_tarski(k1_mcart_1(A_495),k2_mcart_1(A_495)) = A_495
      | ~ v1_relat_1(B_496)
      | v1_xboole_0(B_496)
      | ~ m1_subset_1(A_495,B_496) ) ),
    inference(resolution,[status(thm)],[c_8,c_332])).

tff(c_7900,plain,
    ( k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_3','#skF_4','#skF_5'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_7886])).

tff(c_7909,plain,
    ( k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_7900])).

tff(c_7910,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7909])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_zfmisc_1(k3_zfmisc_1(A_17,B_18,C_19),D_20) = k4_zfmisc_1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_253,plain,(
    ! [A_128,B_129,C_130] :
      ( r2_hidden(k1_mcart_1(A_128),B_129)
      | ~ r2_hidden(A_128,k2_zfmisc_1(B_129,C_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_563,plain,(
    ! [B_194,C_195] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_194,C_195))),B_194)
      | v1_xboole_0(k2_zfmisc_1(B_194,C_195)) ) ),
    inference(resolution,[status(thm)],[c_4,c_253])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_864,plain,(
    ! [B_209,C_210] :
      ( ~ v1_xboole_0(B_209)
      | v1_xboole_0(k2_zfmisc_1(B_209,C_210)) ) ),
    inference(resolution,[status(thm)],[c_563,c_2])).

tff(c_4223,plain,(
    ! [A_392,B_393,C_394,D_395] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_392,B_393,C_394))
      | v1_xboole_0(k4_zfmisc_1(A_392,B_393,C_394,D_395)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_864])).

tff(c_90,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_2'(A_88),A_88)
      | k1_xboole_0 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_98,plain,(
    ! [A_88] :
      ( ~ v1_xboole_0(A_88)
      | k1_xboole_0 = A_88 ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_4290,plain,(
    ! [A_392,B_393,C_394,D_395] :
      ( k4_zfmisc_1(A_392,B_393,C_394,D_395) = k1_xboole_0
      | ~ v1_xboole_0(k3_zfmisc_1(A_392,B_393,C_394)) ) ),
    inference(resolution,[status(thm)],[c_4223,c_98])).

tff(c_8044,plain,(
    ! [D_497] : k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_497) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7910,c_4290])).

tff(c_40,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k4_zfmisc_1(A_54,B_55,C_56,D_57) != k1_xboole_0
      | k1_xboole_0 = D_57
      | k1_xboole_0 = C_56
      | k1_xboole_0 = B_55
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8082,plain,(
    ! [D_497] :
      ( k1_xboole_0 = D_497
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8044,c_40])).

tff(c_8131,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_8082])).

tff(c_8119,plain,(
    ! [D_497] : k1_xboole_0 = D_497 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_8082])).

tff(c_8600,plain,(
    ! [D_4561] : D_4561 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8131,c_8119])).

tff(c_8774,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_8600,c_58])).

tff(c_8776,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7909])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_277,plain,(
    ! [A_134,C_135,B_136] :
      ( r2_hidden(k2_mcart_1(A_134),C_135)
      | ~ r2_hidden(A_134,k2_zfmisc_1(B_136,C_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_292,plain,(
    ! [A_137,C_138,A_139,B_140] :
      ( r2_hidden(k2_mcart_1(A_137),C_138)
      | ~ r2_hidden(A_137,k3_zfmisc_1(A_139,B_140,C_138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_277])).

tff(c_38229,plain,(
    ! [A_7194,C_7195,A_7196,B_7197] :
      ( r2_hidden(k2_mcart_1(A_7194),C_7195)
      | v1_xboole_0(k3_zfmisc_1(A_7196,B_7197,C_7195))
      | ~ m1_subset_1(A_7194,k3_zfmisc_1(A_7196,B_7197,C_7195)) ) ),
    inference(resolution,[status(thm)],[c_8,c_292])).

tff(c_38311,plain,
    ( r2_hidden(k2_mcart_1('#skF_7'),'#skF_5')
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_38229])).

tff(c_38328,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_8776,c_38311])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38348,plain,(
    m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_38328,c_6])).

tff(c_8775,plain,(
    k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7909])).

tff(c_518,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k5_mcart_1(A_182,B_183,C_184,D_185) = k1_mcart_1(k1_mcart_1(D_185))
      | ~ m1_subset_1(D_185,k3_zfmisc_1(A_182,B_183,C_184))
      | k1_xboole_0 = C_184
      | k1_xboole_0 = B_183
      | k1_xboole_0 = A_182 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_529,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_518])).

tff(c_534,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_529])).

tff(c_5883,plain,(
    ! [A_440,B_441,C_442] :
      ( r2_hidden(k1_mcart_1(A_440),B_441)
      | v1_xboole_0(k2_zfmisc_1(B_441,C_442))
      | ~ m1_subset_1(A_440,k2_zfmisc_1(B_441,C_442)) ) ),
    inference(resolution,[status(thm)],[c_8,c_253])).

tff(c_5919,plain,(
    ! [A_440,A_14,B_15,C_16] :
      ( r2_hidden(k1_mcart_1(A_440),k2_zfmisc_1(A_14,B_15))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16))
      | ~ m1_subset_1(A_440,k3_zfmisc_1(A_14,B_15,C_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_5883])).

tff(c_74342,plain,(
    ! [A_7601,A_7602,B_7603,C_7604] :
      ( r2_hidden(k1_mcart_1(A_7601),k2_zfmisc_1(A_7602,B_7603))
      | v1_xboole_0(k3_zfmisc_1(A_7602,B_7603,C_7604))
      | ~ m1_subset_1(A_7601,k3_zfmisc_1(A_7602,B_7603,C_7604)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5919])).

tff(c_74447,plain,
    ( r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_74342])).

tff(c_74466,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_8776,c_74447])).

tff(c_20,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k1_mcart_1(A_21),B_22)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74476,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_74466,c_20])).

tff(c_74491,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_74476])).

tff(c_74551,plain,(
    m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_74491,c_6])).

tff(c_540,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k6_mcart_1(A_186,B_187,C_188,D_189) = k2_mcart_1(k1_mcart_1(D_189))
      | ~ m1_subset_1(D_189,k3_zfmisc_1(A_186,B_187,C_188))
      | k1_xboole_0 = C_188
      | k1_xboole_0 = B_187
      | k1_xboole_0 = A_186 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_551,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_540])).

tff(c_556,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_551])).

tff(c_18,plain,(
    ! [A_21,C_23,B_22] :
      ( r2_hidden(k2_mcart_1(A_21),C_23)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74474,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_74466,c_18])).

tff(c_74489,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_74474])).

tff(c_74529,plain,(
    m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_74489,c_6])).

tff(c_26,plain,(
    ! [A_29,B_30] :
      ( k4_tarski(k1_mcart_1(A_29),k2_mcart_1(A_29)) = A_29
      | ~ r2_hidden(A_29,B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74472,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_7')),k2_mcart_1(k1_mcart_1('#skF_7'))) = k1_mcart_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_74466,c_26])).

tff(c_74487,plain,(
    k4_tarski(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')) = k1_mcart_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_534,c_556,c_74472])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k4_tarski(k4_tarski(A_11,B_12),C_13) = k3_mcart_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77473,plain,(
    ! [C_7668] : k3_mcart_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),C_7668) = k4_tarski(k1_mcart_1('#skF_7'),C_7668) ),
    inference(superposition,[status(thm),theory(equality)],[c_74487,c_12])).

tff(c_62,plain,(
    ! [H_73,F_67,G_71] :
      ( H_73 = '#skF_6'
      | k3_mcart_1(F_67,G_71,H_73) != '#skF_7'
      | ~ m1_subset_1(H_73,'#skF_5')
      | ~ m1_subset_1(G_71,'#skF_4')
      | ~ m1_subset_1(F_67,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_77492,plain,(
    ! [C_7668] :
      ( C_7668 = '#skF_6'
      | k4_tarski(k1_mcart_1('#skF_7'),C_7668) != '#skF_7'
      | ~ m1_subset_1(C_7668,'#skF_5')
      | ~ m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4')
      | ~ m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77473,c_62])).

tff(c_77504,plain,(
    ! [C_7669] :
      ( C_7669 = '#skF_6'
      | k4_tarski(k1_mcart_1('#skF_7'),C_7669) != '#skF_7'
      | ~ m1_subset_1(C_7669,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74551,c_74529,c_77492])).

tff(c_77507,plain,
    ( k2_mcart_1('#skF_7') = '#skF_6'
    | ~ m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8775,c_77504])).

tff(c_77510,plain,(
    k2_mcart_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38348,c_77507])).

tff(c_77512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_513,c_77510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:18:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.20/7.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.20/7.76  
% 15.20/7.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.20/7.76  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 15.20/7.76  
% 15.20/7.76  %Foreground sorts:
% 15.20/7.76  
% 15.20/7.76  
% 15.20/7.76  %Background operators:
% 15.20/7.76  
% 15.20/7.76  
% 15.20/7.76  %Foreground operators:
% 15.20/7.76  tff('#skF_2', type, '#skF_2': $i > $i).
% 15.20/7.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.20/7.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.20/7.76  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.20/7.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.20/7.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.20/7.76  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 15.20/7.76  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 15.20/7.76  tff('#skF_7', type, '#skF_7': $i).
% 15.20/7.76  tff('#skF_5', type, '#skF_5': $i).
% 15.20/7.76  tff('#skF_6', type, '#skF_6': $i).
% 15.20/7.76  tff('#skF_3', type, '#skF_3': $i).
% 15.20/7.76  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 15.20/7.76  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 15.20/7.76  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 15.20/7.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.20/7.76  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 15.20/7.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.20/7.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.20/7.76  tff('#skF_4', type, '#skF_4': $i).
% 15.20/7.76  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 15.20/7.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.20/7.76  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 15.20/7.76  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 15.20/7.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.20/7.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.20/7.76  
% 15.35/7.78  tff(f_149, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 15.35/7.78  tff(f_106, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 15.35/7.78  tff(f_47, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 15.35/7.78  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.35/7.78  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 15.35/7.78  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 15.35/7.78  tff(f_49, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 15.35/7.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 15.35/7.78  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 15.35/7.78  tff(f_86, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 15.35/7.78  tff(f_121, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 15.35/7.78  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 15.35/7.78  tff(f_45, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 15.35/7.78  tff(c_60, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_149])).
% 15.35/7.78  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_149])).
% 15.35/7.78  tff(c_56, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_149])).
% 15.35/7.78  tff(c_64, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 15.35/7.78  tff(c_496, plain, (![A_178, B_179, C_180, D_181]: (k7_mcart_1(A_178, B_179, C_180, D_181)=k2_mcart_1(D_181) | ~m1_subset_1(D_181, k3_zfmisc_1(A_178, B_179, C_180)) | k1_xboole_0=C_180 | k1_xboole_0=B_179 | k1_xboole_0=A_178)), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.35/7.78  tff(c_507, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_64, c_496])).
% 15.35/7.78  tff(c_512, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_507])).
% 15.35/7.78  tff(c_54, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_149])).
% 15.35/7.78  tff(c_513, plain, (k2_mcart_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_512, c_54])).
% 15.35/7.78  tff(c_197, plain, (![A_110, B_111, C_112]: (k2_zfmisc_1(k2_zfmisc_1(A_110, B_111), C_112)=k3_zfmisc_1(A_110, B_111, C_112))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.35/7.78  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.35/7.78  tff(c_205, plain, (![A_110, B_111, C_112]: (v1_relat_1(k3_zfmisc_1(A_110, B_111, C_112)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_10])).
% 15.35/7.78  tff(c_8, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.35/7.78  tff(c_332, plain, (![A_149, B_150]: (k4_tarski(k1_mcart_1(A_149), k2_mcart_1(A_149))=A_149 | ~r2_hidden(A_149, B_150) | ~v1_relat_1(B_150))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.35/7.78  tff(c_7886, plain, (![A_495, B_496]: (k4_tarski(k1_mcart_1(A_495), k2_mcart_1(A_495))=A_495 | ~v1_relat_1(B_496) | v1_xboole_0(B_496) | ~m1_subset_1(A_495, B_496))), inference(resolution, [status(thm)], [c_8, c_332])).
% 15.35/7.78  tff(c_7900, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~v1_relat_1(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_7886])).
% 15.35/7.78  tff(c_7909, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_7900])).
% 15.35/7.78  tff(c_7910, plain, (v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_7909])).
% 15.35/7.78  tff(c_16, plain, (![A_17, B_18, C_19, D_20]: (k2_zfmisc_1(k3_zfmisc_1(A_17, B_18, C_19), D_20)=k4_zfmisc_1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.35/7.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.35/7.78  tff(c_253, plain, (![A_128, B_129, C_130]: (r2_hidden(k1_mcart_1(A_128), B_129) | ~r2_hidden(A_128, k2_zfmisc_1(B_129, C_130)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.35/7.78  tff(c_563, plain, (![B_194, C_195]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_194, C_195))), B_194) | v1_xboole_0(k2_zfmisc_1(B_194, C_195)))), inference(resolution, [status(thm)], [c_4, c_253])).
% 15.35/7.78  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.35/7.78  tff(c_864, plain, (![B_209, C_210]: (~v1_xboole_0(B_209) | v1_xboole_0(k2_zfmisc_1(B_209, C_210)))), inference(resolution, [status(thm)], [c_563, c_2])).
% 15.35/7.78  tff(c_4223, plain, (![A_392, B_393, C_394, D_395]: (~v1_xboole_0(k3_zfmisc_1(A_392, B_393, C_394)) | v1_xboole_0(k4_zfmisc_1(A_392, B_393, C_394, D_395)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_864])).
% 15.35/7.78  tff(c_90, plain, (![A_88]: (r2_hidden('#skF_2'(A_88), A_88) | k1_xboole_0=A_88)), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.35/7.78  tff(c_98, plain, (![A_88]: (~v1_xboole_0(A_88) | k1_xboole_0=A_88)), inference(resolution, [status(thm)], [c_90, c_2])).
% 15.35/7.78  tff(c_4290, plain, (![A_392, B_393, C_394, D_395]: (k4_zfmisc_1(A_392, B_393, C_394, D_395)=k1_xboole_0 | ~v1_xboole_0(k3_zfmisc_1(A_392, B_393, C_394)))), inference(resolution, [status(thm)], [c_4223, c_98])).
% 15.35/7.78  tff(c_8044, plain, (![D_497]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_497)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7910, c_4290])).
% 15.35/7.78  tff(c_40, plain, (![A_54, B_55, C_56, D_57]: (k4_zfmisc_1(A_54, B_55, C_56, D_57)!=k1_xboole_0 | k1_xboole_0=D_57 | k1_xboole_0=C_56 | k1_xboole_0=B_55 | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_121])).
% 15.35/7.78  tff(c_8082, plain, (![D_497]: (k1_xboole_0=D_497 | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8044, c_40])).
% 15.35/7.78  tff(c_8131, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_8082])).
% 15.35/7.78  tff(c_8119, plain, (![D_497]: (k1_xboole_0=D_497)), inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_8082])).
% 15.35/7.78  tff(c_8600, plain, (![D_4561]: (D_4561='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8131, c_8119])).
% 15.35/7.78  tff(c_8774, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_8600, c_58])).
% 15.35/7.78  tff(c_8776, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_7909])).
% 15.35/7.78  tff(c_14, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.35/7.78  tff(c_277, plain, (![A_134, C_135, B_136]: (r2_hidden(k2_mcart_1(A_134), C_135) | ~r2_hidden(A_134, k2_zfmisc_1(B_136, C_135)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.35/7.78  tff(c_292, plain, (![A_137, C_138, A_139, B_140]: (r2_hidden(k2_mcart_1(A_137), C_138) | ~r2_hidden(A_137, k3_zfmisc_1(A_139, B_140, C_138)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_277])).
% 15.35/7.78  tff(c_38229, plain, (![A_7194, C_7195, A_7196, B_7197]: (r2_hidden(k2_mcart_1(A_7194), C_7195) | v1_xboole_0(k3_zfmisc_1(A_7196, B_7197, C_7195)) | ~m1_subset_1(A_7194, k3_zfmisc_1(A_7196, B_7197, C_7195)))), inference(resolution, [status(thm)], [c_8, c_292])).
% 15.35/7.78  tff(c_38311, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_5') | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_38229])).
% 15.35/7.78  tff(c_38328, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_8776, c_38311])).
% 15.35/7.78  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.35/7.78  tff(c_38348, plain, (m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_38328, c_6])).
% 15.35/7.78  tff(c_8775, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(splitRight, [status(thm)], [c_7909])).
% 15.35/7.78  tff(c_518, plain, (![A_182, B_183, C_184, D_185]: (k5_mcart_1(A_182, B_183, C_184, D_185)=k1_mcart_1(k1_mcart_1(D_185)) | ~m1_subset_1(D_185, k3_zfmisc_1(A_182, B_183, C_184)) | k1_xboole_0=C_184 | k1_xboole_0=B_183 | k1_xboole_0=A_182)), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.35/7.78  tff(c_529, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_64, c_518])).
% 15.35/7.78  tff(c_534, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_529])).
% 15.35/7.78  tff(c_5883, plain, (![A_440, B_441, C_442]: (r2_hidden(k1_mcart_1(A_440), B_441) | v1_xboole_0(k2_zfmisc_1(B_441, C_442)) | ~m1_subset_1(A_440, k2_zfmisc_1(B_441, C_442)))), inference(resolution, [status(thm)], [c_8, c_253])).
% 15.35/7.78  tff(c_5919, plain, (![A_440, A_14, B_15, C_16]: (r2_hidden(k1_mcart_1(A_440), k2_zfmisc_1(A_14, B_15)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)) | ~m1_subset_1(A_440, k3_zfmisc_1(A_14, B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_5883])).
% 15.35/7.78  tff(c_74342, plain, (![A_7601, A_7602, B_7603, C_7604]: (r2_hidden(k1_mcart_1(A_7601), k2_zfmisc_1(A_7602, B_7603)) | v1_xboole_0(k3_zfmisc_1(A_7602, B_7603, C_7604)) | ~m1_subset_1(A_7601, k3_zfmisc_1(A_7602, B_7603, C_7604)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5919])).
% 15.35/7.78  tff(c_74447, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_74342])).
% 15.35/7.78  tff(c_74466, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_8776, c_74447])).
% 15.35/7.78  tff(c_20, plain, (![A_21, B_22, C_23]: (r2_hidden(k1_mcart_1(A_21), B_22) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.35/7.78  tff(c_74476, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')), '#skF_3')), inference(resolution, [status(thm)], [c_74466, c_20])).
% 15.35/7.78  tff(c_74491, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_534, c_74476])).
% 15.35/7.78  tff(c_74551, plain, (m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(resolution, [status(thm)], [c_74491, c_6])).
% 15.35/7.78  tff(c_540, plain, (![A_186, B_187, C_188, D_189]: (k6_mcart_1(A_186, B_187, C_188, D_189)=k2_mcart_1(k1_mcart_1(D_189)) | ~m1_subset_1(D_189, k3_zfmisc_1(A_186, B_187, C_188)) | k1_xboole_0=C_188 | k1_xboole_0=B_187 | k1_xboole_0=A_186)), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.35/7.78  tff(c_551, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_64, c_540])).
% 15.35/7.78  tff(c_556, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_551])).
% 15.35/7.78  tff(c_18, plain, (![A_21, C_23, B_22]: (r2_hidden(k2_mcart_1(A_21), C_23) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.35/7.78  tff(c_74474, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_4')), inference(resolution, [status(thm)], [c_74466, c_18])).
% 15.35/7.78  tff(c_74489, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_556, c_74474])).
% 15.35/7.78  tff(c_74529, plain, (m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_74489, c_6])).
% 15.35/7.78  tff(c_26, plain, (![A_29, B_30]: (k4_tarski(k1_mcart_1(A_29), k2_mcart_1(A_29))=A_29 | ~r2_hidden(A_29, B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.35/7.78  tff(c_74472, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_7')), k2_mcart_1(k1_mcart_1('#skF_7')))=k1_mcart_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_74466, c_26])).
% 15.35/7.78  tff(c_74487, plain, (k4_tarski(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))=k1_mcart_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_534, c_556, c_74472])).
% 15.35/7.78  tff(c_12, plain, (![A_11, B_12, C_13]: (k4_tarski(k4_tarski(A_11, B_12), C_13)=k3_mcart_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.35/7.78  tff(c_77473, plain, (![C_7668]: (k3_mcart_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), C_7668)=k4_tarski(k1_mcart_1('#skF_7'), C_7668))), inference(superposition, [status(thm), theory('equality')], [c_74487, c_12])).
% 15.35/7.78  tff(c_62, plain, (![H_73, F_67, G_71]: (H_73='#skF_6' | k3_mcart_1(F_67, G_71, H_73)!='#skF_7' | ~m1_subset_1(H_73, '#skF_5') | ~m1_subset_1(G_71, '#skF_4') | ~m1_subset_1(F_67, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 15.35/7.78  tff(c_77492, plain, (![C_7668]: (C_7668='#skF_6' | k4_tarski(k1_mcart_1('#skF_7'), C_7668)!='#skF_7' | ~m1_subset_1(C_7668, '#skF_5') | ~m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_77473, c_62])).
% 15.35/7.78  tff(c_77504, plain, (![C_7669]: (C_7669='#skF_6' | k4_tarski(k1_mcart_1('#skF_7'), C_7669)!='#skF_7' | ~m1_subset_1(C_7669, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74551, c_74529, c_77492])).
% 15.35/7.78  tff(c_77507, plain, (k2_mcart_1('#skF_7')='#skF_6' | ~m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8775, c_77504])).
% 15.35/7.78  tff(c_77510, plain, (k2_mcart_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38348, c_77507])).
% 15.35/7.78  tff(c_77512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_513, c_77510])).
% 15.35/7.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.35/7.78  
% 15.35/7.78  Inference rules
% 15.35/7.78  ----------------------
% 15.35/7.78  #Ref     : 0
% 15.35/7.78  #Sup     : 20136
% 15.35/7.78  #Fact    : 0
% 15.35/7.78  #Define  : 0
% 15.35/7.78  #Split   : 5
% 15.35/7.78  #Chain   : 0
% 15.35/7.78  #Close   : 0
% 15.35/7.78  
% 15.35/7.78  Ordering : KBO
% 15.35/7.78  
% 15.35/7.78  Simplification rules
% 15.35/7.78  ----------------------
% 15.35/7.78  #Subsume      : 2159
% 15.35/7.78  #Demod        : 17317
% 15.35/7.78  #Tautology    : 15092
% 15.35/7.78  #SimpNegUnit  : 142
% 15.35/7.78  #BackRed      : 12
% 15.35/7.78  
% 15.35/7.78  #Partial instantiations: 540
% 15.35/7.78  #Strategies tried      : 1
% 15.35/7.78  
% 15.35/7.78  Timing (in seconds)
% 15.35/7.78  ----------------------
% 15.35/7.78  Preprocessing        : 0.35
% 15.35/7.78  Parsing              : 0.19
% 15.35/7.78  CNF conversion       : 0.03
% 15.35/7.78  Main loop            : 6.62
% 15.35/7.78  Inferencing          : 1.53
% 15.35/7.78  Reduction            : 2.14
% 15.35/7.78  Demodulation         : 1.58
% 15.35/7.78  BG Simplification    : 0.15
% 15.35/7.78  Subsumption          : 2.45
% 15.35/7.78  Abstraction          : 0.21
% 15.35/7.78  MUC search           : 0.00
% 15.35/7.78  Cooper               : 0.00
% 15.35/7.78  Total                : 7.02
% 15.35/7.78  Index Insertion      : 0.00
% 15.35/7.78  Index Deletion       : 0.00
% 15.35/7.78  Index Matching       : 0.00
% 15.35/7.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
