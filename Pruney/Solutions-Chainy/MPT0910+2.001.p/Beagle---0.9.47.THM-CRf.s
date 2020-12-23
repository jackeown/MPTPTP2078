%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:59 EST 2020

% Result     : Theorem 11.75s
% Output     : CNFRefutation 12.00s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 665 expanded)
%              Number of leaves         :   40 ( 235 expanded)
%              Depth                    :   15
%              Number of atoms          :  256 (2073 expanded)
%              Number of equality atoms :   99 ( 775 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = G ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k6_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_18,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_519,plain,(
    ! [A_159,B_160,C_161] :
      ( k4_tarski('#skF_1'(A_159,B_160,C_161),'#skF_2'(A_159,B_160,C_161)) = A_159
      | ~ r2_hidden(A_159,k2_zfmisc_1(B_160,C_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [C_22,D_23,A_9] :
      ( k4_tarski(C_22,D_23) != '#skF_3'(A_9)
      | v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_532,plain,(
    ! [A_159,A_9,B_160,C_161] :
      ( A_159 != '#skF_3'(A_9)
      | v1_relat_1(A_9)
      | ~ r2_hidden(A_159,k2_zfmisc_1(B_160,C_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_16])).

tff(c_724,plain,(
    ! [A_183,B_184,C_185] :
      ( v1_relat_1(A_183)
      | ~ r2_hidden('#skF_3'(A_183),k2_zfmisc_1(B_184,C_185)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_532])).

tff(c_735,plain,(
    ! [B_184,C_185] : v1_relat_1(k2_zfmisc_1(B_184,C_185)) ),
    inference(resolution,[status(thm)],[c_18,c_724])).

tff(c_60,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_127,plain,(
    ! [B_81,A_82] :
      ( v1_xboole_0(B_81)
      | ~ m1_subset_1(B_81,A_82)
      | ~ v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_127])).

tff(c_138,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r2_hidden(B_8,A_7)
      | ~ m1_subset_1(B_8,A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_213,plain,(
    ! [A_112,B_113,C_114] : k2_zfmisc_1(k2_zfmisc_1(A_112,B_113),C_114) = k3_zfmisc_1(A_112,B_113,C_114) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden(k1_mcart_1(A_37),B_38)
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_38,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1856,plain,(
    ! [A_296,A_297,B_298,C_299] :
      ( r2_hidden(k1_mcart_1(A_296),k2_zfmisc_1(A_297,B_298))
      | ~ r2_hidden(A_296,k3_zfmisc_1(A_297,B_298,C_299)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_28])).

tff(c_20169,plain,(
    ! [B_1099,A_1100,B_1101,C_1102] :
      ( r2_hidden(k1_mcart_1(B_1099),k2_zfmisc_1(A_1100,B_1101))
      | ~ m1_subset_1(B_1099,k3_zfmisc_1(A_1100,B_1101,C_1102))
      | v1_xboole_0(k3_zfmisc_1(A_1100,B_1101,C_1102)) ) ),
    inference(resolution,[status(thm)],[c_8,c_1856])).

tff(c_20209,plain,
    ( r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_6','#skF_7'))
    | v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_20169])).

tff(c_20232,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_20209])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(B_8,A_7)
      | ~ v1_xboole_0(B_8)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_30,B_31,C_32] : k2_zfmisc_1(k2_zfmisc_1(A_30,B_31),C_32) = k3_zfmisc_1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_736,plain,(
    ! [B_186,C_187] : v1_relat_1(k2_zfmisc_1(B_186,C_187)) ),
    inference(resolution,[status(thm)],[c_18,c_724])).

tff(c_738,plain,(
    ! [A_30,B_31,C_32] : v1_relat_1(k3_zfmisc_1(A_30,B_31,C_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_736])).

tff(c_332,plain,(
    ! [A_128,B_129] :
      ( k4_tarski(k1_mcart_1(A_128),k2_mcart_1(A_128)) = A_128
      | ~ r2_hidden(A_128,B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3066,plain,(
    ! [B_359,A_360] :
      ( k4_tarski(k1_mcart_1(B_359),k2_mcart_1(B_359)) = B_359
      | ~ v1_relat_1(A_360)
      | ~ m1_subset_1(B_359,A_360)
      | v1_xboole_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_8,c_332])).

tff(c_3084,plain,
    ( k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_3066])).

tff(c_3101,plain,
    ( k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_3084])).

tff(c_3102,plain,(
    k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_3101])).

tff(c_20,plain,(
    ! [A_27,B_28,C_29] : k4_tarski(k4_tarski(A_27,B_28),C_29) = k3_mcart_1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3182,plain,(
    ! [C_366] : k3_mcart_1(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10'),C_366) = k4_tarski('#skF_10',C_366) ),
    inference(superposition,[status(thm),theory(equality)],[c_3102,c_20])).

tff(c_58,plain,(
    ! [G_63,F_59,H_65] :
      ( G_63 = '#skF_9'
      | k3_mcart_1(F_59,G_63,H_65) != '#skF_10'
      | ~ m1_subset_1(H_65,'#skF_8')
      | ~ m1_subset_1(G_63,'#skF_7')
      | ~ m1_subset_1(F_59,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3212,plain,(
    ! [C_366] :
      ( k2_mcart_1('#skF_10') = '#skF_9'
      | k4_tarski('#skF_10',C_366) != '#skF_10'
      | ~ m1_subset_1(C_366,'#skF_8')
      | ~ m1_subset_1(k2_mcart_1('#skF_10'),'#skF_7')
      | ~ m1_subset_1(k1_mcart_1('#skF_10'),'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3182,c_58])).

tff(c_3410,plain,(
    ~ m1_subset_1(k1_mcart_1('#skF_10'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3212])).

tff(c_3414,plain,
    ( ~ v1_xboole_0(k1_mcart_1('#skF_10'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_3410])).

tff(c_3415,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3414])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_681,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( k5_mcart_1(A_179,B_180,C_181,D_182) = k1_mcart_1(k1_mcart_1(D_182))
      | ~ m1_subset_1(D_182,k3_zfmisc_1(A_179,B_180,C_181))
      | k1_xboole_0 = C_181
      | k1_xboole_0 = B_180
      | k1_xboole_0 = A_179 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_700,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_681])).

tff(c_716,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_700])).

tff(c_20257,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_20232,c_28])).

tff(c_20278,plain,(
    r2_hidden(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_20257])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(B_8,A_7)
      | ~ r2_hidden(B_8,A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20292,plain,
    ( m1_subset_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_20278,c_6])).

tff(c_20298,plain,(
    m1_subset_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_3415,c_20292])).

tff(c_366,plain,(
    ! [A_135,B_136] :
      ( k4_tarski('#skF_4'(A_135,B_136),'#skF_5'(A_135,B_136)) = B_136
      | ~ r2_hidden(B_136,A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_46,plain,(
    ! [A_50,B_51] : k1_mcart_1(k4_tarski(A_50,B_51)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_381,plain,(
    ! [B_136,A_135] :
      ( k1_mcart_1(B_136) = '#skF_4'(A_135,B_136)
      | ~ r2_hidden(B_136,A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_46])).

tff(c_20250,plain,
    ( '#skF_4'(k2_zfmisc_1('#skF_6','#skF_7'),k1_mcart_1('#skF_10')) = k1_mcart_1(k1_mcart_1('#skF_10'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_20232,c_381])).

tff(c_20270,plain,(
    '#skF_4'(k2_zfmisc_1('#skF_6','#skF_7'),k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_716,c_20250])).

tff(c_479,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( m1_subset_1(k6_mcart_1(A_150,B_151,C_152,D_153),B_151)
      | ~ m1_subset_1(D_153,k3_zfmisc_1(A_150,B_151,C_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( v1_xboole_0(B_8)
      | ~ m1_subset_1(B_8,A_7)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3762,plain,(
    ! [A_400,B_401,C_402,D_403] :
      ( v1_xboole_0(k6_mcart_1(A_400,B_401,C_402,D_403))
      | ~ v1_xboole_0(B_401)
      | ~ m1_subset_1(D_403,k3_zfmisc_1(A_400,B_401,C_402)) ) ),
    inference(resolution,[status(thm)],[c_479,c_12])).

tff(c_3809,plain,
    ( v1_xboole_0(k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_3762])).

tff(c_3810,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3809])).

tff(c_746,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( k6_mcart_1(A_191,B_192,C_193,D_194) = k2_mcart_1(k1_mcart_1(D_194))
      | ~ m1_subset_1(D_194,k3_zfmisc_1(A_191,B_192,C_193))
      | k1_xboole_0 = C_193
      | k1_xboole_0 = B_192
      | k1_xboole_0 = A_191 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_765,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_746])).

tff(c_782,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_765])).

tff(c_26,plain,(
    ! [A_37,C_39,B_38] :
      ( r2_hidden(k2_mcart_1(A_37),C_39)
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_38,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20259,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_20232,c_26])).

tff(c_20280,plain,(
    r2_hidden(k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_20259])).

tff(c_20309,plain,
    ( m1_subset_1(k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10'),'#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_20280,c_6])).

tff(c_20315,plain,(
    m1_subset_1(k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_3810,c_20309])).

tff(c_48,plain,(
    ! [A_50,B_51] : k2_mcart_1(k4_tarski(A_50,B_51)) = B_51 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_378,plain,(
    ! [B_136,A_135] :
      ( k2_mcart_1(B_136) = '#skF_5'(A_135,B_136)
      | ~ r2_hidden(B_136,A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_48])).

tff(c_20253,plain,
    ( '#skF_5'(k2_zfmisc_1('#skF_6','#skF_7'),k1_mcart_1('#skF_10')) = k2_mcart_1(k1_mcart_1('#skF_10'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_20232,c_378])).

tff(c_20273,plain,(
    '#skF_5'(k2_zfmisc_1('#skF_6','#skF_7'),k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_782,c_20253])).

tff(c_3970,plain,(
    ! [A_415,B_416,C_417] :
      ( k3_mcart_1('#skF_4'(A_415,B_416),'#skF_5'(A_415,B_416),C_417) = k4_tarski(B_416,C_417)
      | ~ r2_hidden(B_416,A_415)
      | ~ v1_relat_1(A_415) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_20])).

tff(c_4146,plain,(
    ! [A_422,B_423,C_424] :
      ( '#skF_5'(A_422,B_423) = '#skF_9'
      | k4_tarski(B_423,C_424) != '#skF_10'
      | ~ m1_subset_1(C_424,'#skF_8')
      | ~ m1_subset_1('#skF_5'(A_422,B_423),'#skF_7')
      | ~ m1_subset_1('#skF_4'(A_422,B_423),'#skF_6')
      | ~ r2_hidden(B_423,A_422)
      | ~ v1_relat_1(A_422) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3970,c_58])).

tff(c_4155,plain,(
    ! [A_422] :
      ( '#skF_5'(A_422,k1_mcart_1('#skF_10')) = '#skF_9'
      | ~ m1_subset_1(k2_mcart_1('#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_5'(A_422,k1_mcart_1('#skF_10')),'#skF_7')
      | ~ m1_subset_1('#skF_4'(A_422,k1_mcart_1('#skF_10')),'#skF_6')
      | ~ r2_hidden(k1_mcart_1('#skF_10'),A_422)
      | ~ v1_relat_1(A_422) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3102,c_4146])).

tff(c_4432,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4155])).

tff(c_4444,plain,
    ( ~ v1_xboole_0(k2_mcart_1('#skF_10'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_4432])).

tff(c_4445,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4444])).

tff(c_232,plain,(
    ! [A_115,C_116,A_117,B_118] :
      ( r2_hidden(k2_mcart_1(A_115),C_116)
      | ~ r2_hidden(A_115,k3_zfmisc_1(A_117,B_118,C_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_26])).

tff(c_11139,plain,(
    ! [B_724,C_725,A_726,B_727] :
      ( r2_hidden(k2_mcart_1(B_724),C_725)
      | ~ m1_subset_1(B_724,k3_zfmisc_1(A_726,B_727,C_725))
      | v1_xboole_0(k3_zfmisc_1(A_726,B_727,C_725)) ) ),
    inference(resolution,[status(thm)],[c_8,c_232])).

tff(c_11179,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_8')
    | v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_11139])).

tff(c_11202,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_11179])).

tff(c_11219,plain,
    ( m1_subset_1(k2_mcart_1('#skF_10'),'#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_11202,c_6])).

tff(c_11226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4445,c_4432,c_11219])).

tff(c_11228,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_4444])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_11233,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_11228,c_2])).

tff(c_11238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_11233])).

tff(c_11239,plain,(
    ! [A_422] :
      ( '#skF_5'(A_422,k1_mcart_1('#skF_10')) = '#skF_9'
      | ~ m1_subset_1('#skF_5'(A_422,k1_mcart_1('#skF_10')),'#skF_7')
      | ~ m1_subset_1('#skF_4'(A_422,k1_mcart_1('#skF_10')),'#skF_6')
      | ~ r2_hidden(k1_mcart_1('#skF_10'),A_422)
      | ~ v1_relat_1(A_422) ) ),
    inference(splitRight,[status(thm)],[c_4155])).

tff(c_22264,plain,
    ( '#skF_5'(k2_zfmisc_1('#skF_6','#skF_7'),k1_mcart_1('#skF_10')) = '#skF_9'
    | ~ m1_subset_1(k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10'),'#skF_7')
    | ~ m1_subset_1('#skF_4'(k2_zfmisc_1('#skF_6','#skF_7'),k1_mcart_1('#skF_10')),'#skF_6')
    | ~ r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20273,c_11239])).

tff(c_22276,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_20232,c_20298,c_20270,c_20315,c_20273,c_22264])).

tff(c_22278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_22276])).

tff(c_22280,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3809])).

tff(c_22283,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_22280,c_2])).

tff(c_22287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_22283])).

tff(c_22289,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_3414])).

tff(c_22292,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_22289,c_2])).

tff(c_22296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_22292])).

tff(c_22297,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_22311,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_22297,c_2])).

tff(c_22318,plain,(
    '#skF_10' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22311,c_56])).

tff(c_22317,plain,(
    '#skF_7' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22311,c_54])).

tff(c_22316,plain,(
    '#skF_10' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22311,c_52])).

tff(c_22298,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_22315,plain,(
    ! [A_1] :
      ( A_1 = '#skF_10'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22311,c_2])).

tff(c_22333,plain,(
    k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_22298,c_22315])).

tff(c_32,plain,(
    ! [A_42,B_43,C_44] :
      ( k3_zfmisc_1(A_42,B_43,C_44) != k1_xboole_0
      | k1_xboole_0 = C_44
      | k1_xboole_0 = B_43
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22659,plain,(
    ! [A_1202,B_1203,C_1204] :
      ( k3_zfmisc_1(A_1202,B_1203,C_1204) != '#skF_10'
      | C_1204 = '#skF_10'
      | B_1203 = '#skF_10'
      | A_1202 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22311,c_22311,c_22311,c_22311,c_32])).

tff(c_22662,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_10'
    | '#skF_10' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_22333,c_22659])).

tff(c_22675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22318,c_22317,c_22316,c_22662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:10:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.75/4.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/4.83  
% 12.00/4.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/4.84  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 12.00/4.84  
% 12.00/4.84  %Foreground sorts:
% 12.00/4.84  
% 12.00/4.84  
% 12.00/4.84  %Background operators:
% 12.00/4.84  
% 12.00/4.84  
% 12.00/4.84  %Foreground operators:
% 12.00/4.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.00/4.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.00/4.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.00/4.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.00/4.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.00/4.84  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 12.00/4.84  tff('#skF_7', type, '#skF_7': $i).
% 12.00/4.84  tff('#skF_10', type, '#skF_10': $i).
% 12.00/4.84  tff('#skF_6', type, '#skF_6': $i).
% 12.00/4.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.00/4.84  tff('#skF_9', type, '#skF_9': $i).
% 12.00/4.84  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 12.00/4.84  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 12.00/4.84  tff('#skF_8', type, '#skF_8': $i).
% 12.00/4.84  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 12.00/4.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.00/4.84  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 12.00/4.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.00/4.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.00/4.84  tff('#skF_3', type, '#skF_3': $i > $i).
% 12.00/4.84  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 12.00/4.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.00/4.84  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 12.00/4.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.00/4.84  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.00/4.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.00/4.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.00/4.84  
% 12.00/4.86  tff(f_139, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 12.00/4.86  tff(f_59, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 12.00/4.86  tff(f_36, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 12.00/4.86  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 12.00/4.86  tff(f_63, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 12.00/4.86  tff(f_73, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 12.00/4.86  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 12.00/4.86  tff(f_61, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 12.00/4.86  tff(f_111, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 12.00/4.86  tff(f_115, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 12.00/4.86  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 12.00/4.86  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 12.00/4.86  tff(f_91, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 12.00/4.86  tff(c_56, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.00/4.86  tff(c_54, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.00/4.86  tff(c_50, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.00/4.86  tff(c_18, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.00/4.86  tff(c_519, plain, (![A_159, B_160, C_161]: (k4_tarski('#skF_1'(A_159, B_160, C_161), '#skF_2'(A_159, B_160, C_161))=A_159 | ~r2_hidden(A_159, k2_zfmisc_1(B_160, C_161)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.00/4.86  tff(c_16, plain, (![C_22, D_23, A_9]: (k4_tarski(C_22, D_23)!='#skF_3'(A_9) | v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.00/4.86  tff(c_532, plain, (![A_159, A_9, B_160, C_161]: (A_159!='#skF_3'(A_9) | v1_relat_1(A_9) | ~r2_hidden(A_159, k2_zfmisc_1(B_160, C_161)))), inference(superposition, [status(thm), theory('equality')], [c_519, c_16])).
% 12.00/4.86  tff(c_724, plain, (![A_183, B_184, C_185]: (v1_relat_1(A_183) | ~r2_hidden('#skF_3'(A_183), k2_zfmisc_1(B_184, C_185)))), inference(reflexivity, [status(thm), theory('equality')], [c_532])).
% 12.00/4.86  tff(c_735, plain, (![B_184, C_185]: (v1_relat_1(k2_zfmisc_1(B_184, C_185)))), inference(resolution, [status(thm)], [c_18, c_724])).
% 12.00/4.86  tff(c_60, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.00/4.86  tff(c_127, plain, (![B_81, A_82]: (v1_xboole_0(B_81) | ~m1_subset_1(B_81, A_82) | ~v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.00/4.86  tff(c_131, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_60, c_127])).
% 12.00/4.86  tff(c_138, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_131])).
% 12.00/4.86  tff(c_8, plain, (![B_8, A_7]: (r2_hidden(B_8, A_7) | ~m1_subset_1(B_8, A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.00/4.86  tff(c_213, plain, (![A_112, B_113, C_114]: (k2_zfmisc_1(k2_zfmisc_1(A_112, B_113), C_114)=k3_zfmisc_1(A_112, B_113, C_114))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.00/4.86  tff(c_28, plain, (![A_37, B_38, C_39]: (r2_hidden(k1_mcart_1(A_37), B_38) | ~r2_hidden(A_37, k2_zfmisc_1(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.00/4.86  tff(c_1856, plain, (![A_296, A_297, B_298, C_299]: (r2_hidden(k1_mcart_1(A_296), k2_zfmisc_1(A_297, B_298)) | ~r2_hidden(A_296, k3_zfmisc_1(A_297, B_298, C_299)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_28])).
% 12.00/4.86  tff(c_20169, plain, (![B_1099, A_1100, B_1101, C_1102]: (r2_hidden(k1_mcart_1(B_1099), k2_zfmisc_1(A_1100, B_1101)) | ~m1_subset_1(B_1099, k3_zfmisc_1(A_1100, B_1101, C_1102)) | v1_xboole_0(k3_zfmisc_1(A_1100, B_1101, C_1102)))), inference(resolution, [status(thm)], [c_8, c_1856])).
% 12.00/4.86  tff(c_20209, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_6', '#skF_7')) | v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_60, c_20169])).
% 12.00/4.86  tff(c_20232, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_138, c_20209])).
% 12.00/4.86  tff(c_10, plain, (![B_8, A_7]: (m1_subset_1(B_8, A_7) | ~v1_xboole_0(B_8) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.00/4.86  tff(c_22, plain, (![A_30, B_31, C_32]: (k2_zfmisc_1(k2_zfmisc_1(A_30, B_31), C_32)=k3_zfmisc_1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.00/4.86  tff(c_736, plain, (![B_186, C_187]: (v1_relat_1(k2_zfmisc_1(B_186, C_187)))), inference(resolution, [status(thm)], [c_18, c_724])).
% 12.00/4.86  tff(c_738, plain, (![A_30, B_31, C_32]: (v1_relat_1(k3_zfmisc_1(A_30, B_31, C_32)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_736])).
% 12.00/4.86  tff(c_332, plain, (![A_128, B_129]: (k4_tarski(k1_mcart_1(A_128), k2_mcart_1(A_128))=A_128 | ~r2_hidden(A_128, B_129) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.00/4.86  tff(c_3066, plain, (![B_359, A_360]: (k4_tarski(k1_mcart_1(B_359), k2_mcart_1(B_359))=B_359 | ~v1_relat_1(A_360) | ~m1_subset_1(B_359, A_360) | v1_xboole_0(A_360))), inference(resolution, [status(thm)], [c_8, c_332])).
% 12.00/4.86  tff(c_3084, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10' | ~v1_relat_1(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_60, c_3066])).
% 12.00/4.86  tff(c_3101, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10' | v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_3084])).
% 12.00/4.86  tff(c_3102, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_138, c_3101])).
% 12.00/4.86  tff(c_20, plain, (![A_27, B_28, C_29]: (k4_tarski(k4_tarski(A_27, B_28), C_29)=k3_mcart_1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.00/4.86  tff(c_3182, plain, (![C_366]: (k3_mcart_1(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'), C_366)=k4_tarski('#skF_10', C_366))), inference(superposition, [status(thm), theory('equality')], [c_3102, c_20])).
% 12.00/4.86  tff(c_58, plain, (![G_63, F_59, H_65]: (G_63='#skF_9' | k3_mcart_1(F_59, G_63, H_65)!='#skF_10' | ~m1_subset_1(H_65, '#skF_8') | ~m1_subset_1(G_63, '#skF_7') | ~m1_subset_1(F_59, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.00/4.86  tff(c_3212, plain, (![C_366]: (k2_mcart_1('#skF_10')='#skF_9' | k4_tarski('#skF_10', C_366)!='#skF_10' | ~m1_subset_1(C_366, '#skF_8') | ~m1_subset_1(k2_mcart_1('#skF_10'), '#skF_7') | ~m1_subset_1(k1_mcart_1('#skF_10'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3182, c_58])).
% 12.00/4.86  tff(c_3410, plain, (~m1_subset_1(k1_mcart_1('#skF_10'), '#skF_6')), inference(splitLeft, [status(thm)], [c_3212])).
% 12.00/4.86  tff(c_3414, plain, (~v1_xboole_0(k1_mcart_1('#skF_10')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_10, c_3410])).
% 12.00/4.86  tff(c_3415, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_3414])).
% 12.00/4.86  tff(c_52, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_139])).
% 12.00/4.86  tff(c_681, plain, (![A_179, B_180, C_181, D_182]: (k5_mcart_1(A_179, B_180, C_181, D_182)=k1_mcart_1(k1_mcart_1(D_182)) | ~m1_subset_1(D_182, k3_zfmisc_1(A_179, B_180, C_181)) | k1_xboole_0=C_181 | k1_xboole_0=B_180 | k1_xboole_0=A_179)), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.00/4.86  tff(c_700, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_60, c_681])).
% 12.00/4.86  tff(c_716, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_700])).
% 12.00/4.86  tff(c_20257, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_6')), inference(resolution, [status(thm)], [c_20232, c_28])).
% 12.00/4.86  tff(c_20278, plain, (r2_hidden(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_716, c_20257])).
% 12.00/4.86  tff(c_6, plain, (![B_8, A_7]: (m1_subset_1(B_8, A_7) | ~r2_hidden(B_8, A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.00/4.86  tff(c_20292, plain, (m1_subset_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10'), '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_20278, c_6])).
% 12.00/4.86  tff(c_20298, plain, (m1_subset_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_3415, c_20292])).
% 12.00/4.86  tff(c_366, plain, (![A_135, B_136]: (k4_tarski('#skF_4'(A_135, B_136), '#skF_5'(A_135, B_136))=B_136 | ~r2_hidden(B_136, A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.00/4.86  tff(c_46, plain, (![A_50, B_51]: (k1_mcart_1(k4_tarski(A_50, B_51))=A_50)), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.00/4.86  tff(c_381, plain, (![B_136, A_135]: (k1_mcart_1(B_136)='#skF_4'(A_135, B_136) | ~r2_hidden(B_136, A_135) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_366, c_46])).
% 12.00/4.86  tff(c_20250, plain, ('#skF_4'(k2_zfmisc_1('#skF_6', '#skF_7'), k1_mcart_1('#skF_10'))=k1_mcart_1(k1_mcart_1('#skF_10')) | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_20232, c_381])).
% 12.00/4.86  tff(c_20270, plain, ('#skF_4'(k2_zfmisc_1('#skF_6', '#skF_7'), k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_735, c_716, c_20250])).
% 12.00/4.86  tff(c_479, plain, (![A_150, B_151, C_152, D_153]: (m1_subset_1(k6_mcart_1(A_150, B_151, C_152, D_153), B_151) | ~m1_subset_1(D_153, k3_zfmisc_1(A_150, B_151, C_152)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.00/4.86  tff(c_12, plain, (![B_8, A_7]: (v1_xboole_0(B_8) | ~m1_subset_1(B_8, A_7) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.00/4.86  tff(c_3762, plain, (![A_400, B_401, C_402, D_403]: (v1_xboole_0(k6_mcart_1(A_400, B_401, C_402, D_403)) | ~v1_xboole_0(B_401) | ~m1_subset_1(D_403, k3_zfmisc_1(A_400, B_401, C_402)))), inference(resolution, [status(thm)], [c_479, c_12])).
% 12.00/4.86  tff(c_3809, plain, (v1_xboole_0(k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_3762])).
% 12.00/4.86  tff(c_3810, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_3809])).
% 12.00/4.86  tff(c_746, plain, (![A_191, B_192, C_193, D_194]: (k6_mcart_1(A_191, B_192, C_193, D_194)=k2_mcart_1(k1_mcart_1(D_194)) | ~m1_subset_1(D_194, k3_zfmisc_1(A_191, B_192, C_193)) | k1_xboole_0=C_193 | k1_xboole_0=B_192 | k1_xboole_0=A_191)), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.00/4.86  tff(c_765, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_60, c_746])).
% 12.00/4.86  tff(c_782, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_765])).
% 12.00/4.86  tff(c_26, plain, (![A_37, C_39, B_38]: (r2_hidden(k2_mcart_1(A_37), C_39) | ~r2_hidden(A_37, k2_zfmisc_1(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.00/4.86  tff(c_20259, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_7')), inference(resolution, [status(thm)], [c_20232, c_26])).
% 12.00/4.86  tff(c_20280, plain, (r2_hidden(k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_782, c_20259])).
% 12.00/4.86  tff(c_20309, plain, (m1_subset_1(k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10'), '#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_20280, c_6])).
% 12.00/4.86  tff(c_20315, plain, (m1_subset_1(k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_3810, c_20309])).
% 12.00/4.86  tff(c_48, plain, (![A_50, B_51]: (k2_mcart_1(k4_tarski(A_50, B_51))=B_51)), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.00/4.86  tff(c_378, plain, (![B_136, A_135]: (k2_mcart_1(B_136)='#skF_5'(A_135, B_136) | ~r2_hidden(B_136, A_135) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_366, c_48])).
% 12.00/4.86  tff(c_20253, plain, ('#skF_5'(k2_zfmisc_1('#skF_6', '#skF_7'), k1_mcart_1('#skF_10'))=k2_mcart_1(k1_mcart_1('#skF_10')) | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_20232, c_378])).
% 12.00/4.86  tff(c_20273, plain, ('#skF_5'(k2_zfmisc_1('#skF_6', '#skF_7'), k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_735, c_782, c_20253])).
% 12.00/4.86  tff(c_3970, plain, (![A_415, B_416, C_417]: (k3_mcart_1('#skF_4'(A_415, B_416), '#skF_5'(A_415, B_416), C_417)=k4_tarski(B_416, C_417) | ~r2_hidden(B_416, A_415) | ~v1_relat_1(A_415))), inference(superposition, [status(thm), theory('equality')], [c_366, c_20])).
% 12.00/4.86  tff(c_4146, plain, (![A_422, B_423, C_424]: ('#skF_5'(A_422, B_423)='#skF_9' | k4_tarski(B_423, C_424)!='#skF_10' | ~m1_subset_1(C_424, '#skF_8') | ~m1_subset_1('#skF_5'(A_422, B_423), '#skF_7') | ~m1_subset_1('#skF_4'(A_422, B_423), '#skF_6') | ~r2_hidden(B_423, A_422) | ~v1_relat_1(A_422))), inference(superposition, [status(thm), theory('equality')], [c_3970, c_58])).
% 12.00/4.86  tff(c_4155, plain, (![A_422]: ('#skF_5'(A_422, k1_mcart_1('#skF_10'))='#skF_9' | ~m1_subset_1(k2_mcart_1('#skF_10'), '#skF_8') | ~m1_subset_1('#skF_5'(A_422, k1_mcart_1('#skF_10')), '#skF_7') | ~m1_subset_1('#skF_4'(A_422, k1_mcart_1('#skF_10')), '#skF_6') | ~r2_hidden(k1_mcart_1('#skF_10'), A_422) | ~v1_relat_1(A_422))), inference(superposition, [status(thm), theory('equality')], [c_3102, c_4146])).
% 12.00/4.86  tff(c_4432, plain, (~m1_subset_1(k2_mcart_1('#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_4155])).
% 12.00/4.86  tff(c_4444, plain, (~v1_xboole_0(k2_mcart_1('#skF_10')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_10, c_4432])).
% 12.00/4.86  tff(c_4445, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_4444])).
% 12.00/4.86  tff(c_232, plain, (![A_115, C_116, A_117, B_118]: (r2_hidden(k2_mcart_1(A_115), C_116) | ~r2_hidden(A_115, k3_zfmisc_1(A_117, B_118, C_116)))), inference(superposition, [status(thm), theory('equality')], [c_213, c_26])).
% 12.00/4.86  tff(c_11139, plain, (![B_724, C_725, A_726, B_727]: (r2_hidden(k2_mcart_1(B_724), C_725) | ~m1_subset_1(B_724, k3_zfmisc_1(A_726, B_727, C_725)) | v1_xboole_0(k3_zfmisc_1(A_726, B_727, C_725)))), inference(resolution, [status(thm)], [c_8, c_232])).
% 12.00/4.86  tff(c_11179, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_8') | v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_60, c_11139])).
% 12.00/4.86  tff(c_11202, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_138, c_11179])).
% 12.00/4.86  tff(c_11219, plain, (m1_subset_1(k2_mcart_1('#skF_10'), '#skF_8') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_11202, c_6])).
% 12.00/4.86  tff(c_11226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4445, c_4432, c_11219])).
% 12.00/4.86  tff(c_11228, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_4444])).
% 12.00/4.86  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.00/4.86  tff(c_11233, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_11228, c_2])).
% 12.00/4.86  tff(c_11238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_11233])).
% 12.00/4.86  tff(c_11239, plain, (![A_422]: ('#skF_5'(A_422, k1_mcart_1('#skF_10'))='#skF_9' | ~m1_subset_1('#skF_5'(A_422, k1_mcart_1('#skF_10')), '#skF_7') | ~m1_subset_1('#skF_4'(A_422, k1_mcart_1('#skF_10')), '#skF_6') | ~r2_hidden(k1_mcart_1('#skF_10'), A_422) | ~v1_relat_1(A_422))), inference(splitRight, [status(thm)], [c_4155])).
% 12.00/4.86  tff(c_22264, plain, ('#skF_5'(k2_zfmisc_1('#skF_6', '#skF_7'), k1_mcart_1('#skF_10'))='#skF_9' | ~m1_subset_1(k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10'), '#skF_7') | ~m1_subset_1('#skF_4'(k2_zfmisc_1('#skF_6', '#skF_7'), k1_mcart_1('#skF_10')), '#skF_6') | ~r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_6', '#skF_7')) | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_20273, c_11239])).
% 12.00/4.86  tff(c_22276, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_735, c_20232, c_20298, c_20270, c_20315, c_20273, c_22264])).
% 12.00/4.86  tff(c_22278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_22276])).
% 12.00/4.86  tff(c_22280, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_3809])).
% 12.00/4.86  tff(c_22283, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_22280, c_2])).
% 12.00/4.86  tff(c_22287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_22283])).
% 12.00/4.86  tff(c_22289, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_3414])).
% 12.00/4.86  tff(c_22292, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_22289, c_2])).
% 12.00/4.86  tff(c_22296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_22292])).
% 12.00/4.86  tff(c_22297, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_131])).
% 12.00/4.86  tff(c_22311, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_22297, c_2])).
% 12.00/4.86  tff(c_22318, plain, ('#skF_10'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22311, c_56])).
% 12.00/4.86  tff(c_22317, plain, ('#skF_7'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_22311, c_54])).
% 12.00/4.86  tff(c_22316, plain, ('#skF_10'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_22311, c_52])).
% 12.00/4.86  tff(c_22298, plain, (v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_131])).
% 12.00/4.86  tff(c_22315, plain, (![A_1]: (A_1='#skF_10' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_22311, c_2])).
% 12.00/4.86  tff(c_22333, plain, (k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')='#skF_10'), inference(resolution, [status(thm)], [c_22298, c_22315])).
% 12.00/4.86  tff(c_32, plain, (![A_42, B_43, C_44]: (k3_zfmisc_1(A_42, B_43, C_44)!=k1_xboole_0 | k1_xboole_0=C_44 | k1_xboole_0=B_43 | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.00/4.86  tff(c_22659, plain, (![A_1202, B_1203, C_1204]: (k3_zfmisc_1(A_1202, B_1203, C_1204)!='#skF_10' | C_1204='#skF_10' | B_1203='#skF_10' | A_1202='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_22311, c_22311, c_22311, c_22311, c_32])).
% 12.00/4.86  tff(c_22662, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_10' | '#skF_10'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_22333, c_22659])).
% 12.00/4.86  tff(c_22675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22318, c_22317, c_22316, c_22662])).
% 12.00/4.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/4.86  
% 12.00/4.86  Inference rules
% 12.00/4.86  ----------------------
% 12.00/4.86  #Ref     : 2
% 12.00/4.86  #Sup     : 6230
% 12.00/4.86  #Fact    : 0
% 12.00/4.86  #Define  : 0
% 12.00/4.86  #Split   : 16
% 12.00/4.86  #Chain   : 0
% 12.00/4.86  #Close   : 0
% 12.00/4.86  
% 12.00/4.86  Ordering : KBO
% 12.00/4.86  
% 12.00/4.86  Simplification rules
% 12.00/4.86  ----------------------
% 12.00/4.86  #Subsume      : 942
% 12.00/4.86  #Demod        : 1020
% 12.00/4.86  #Tautology    : 390
% 12.00/4.86  #SimpNegUnit  : 231
% 12.00/4.86  #BackRed      : 13
% 12.00/4.86  
% 12.00/4.86  #Partial instantiations: 0
% 12.00/4.86  #Strategies tried      : 1
% 12.00/4.86  
% 12.00/4.86  Timing (in seconds)
% 12.00/4.86  ----------------------
% 12.00/4.86  Preprocessing        : 0.34
% 12.00/4.86  Parsing              : 0.18
% 12.00/4.86  CNF conversion       : 0.03
% 12.00/4.86  Main loop            : 3.74
% 12.00/4.86  Inferencing          : 0.96
% 12.00/4.86  Reduction            : 0.98
% 12.00/4.86  Demodulation         : 0.64
% 12.00/4.86  BG Simplification    : 0.14
% 12.00/4.86  Subsumption          : 1.31
% 12.00/4.86  Abstraction          : 0.19
% 12.00/4.86  MUC search           : 0.00
% 12.00/4.86  Cooper               : 0.00
% 12.00/4.86  Total                : 4.12
% 12.00/4.86  Index Insertion      : 0.00
% 12.00/4.86  Index Deletion       : 0.00
% 12.00/4.86  Index Matching       : 0.00
% 12.00/4.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
