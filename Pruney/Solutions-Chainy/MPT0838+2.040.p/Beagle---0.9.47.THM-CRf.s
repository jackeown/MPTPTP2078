%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:14 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 153 expanded)
%              Number of leaves         :   41 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 308 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_517,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_540,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_517])).

tff(c_54,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_542,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_54])).

tff(c_34,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_109,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_112,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_109])).

tff(c_119,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_112])).

tff(c_240,plain,(
    ! [C_101,B_102,A_103] :
      ( v5_relat_1(C_101,B_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_263,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_240])).

tff(c_32,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_399,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_relset_1(A_128,B_129,C_130) = k2_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_422,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_399])).

tff(c_122,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_2'(A_77,B_78),B_78)
      | r1_xboole_0(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_131,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1('#skF_2'(A_77,B_78),B_78)
      | r1_xboole_0(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_122,c_20])).

tff(c_98,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_2'(A_70,B_71),A_70)
      | r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_52,plain,(
    ! [D_55] :
      ( ~ r2_hidden(D_55,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_55,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_357,plain,(
    ! [B_120] :
      ( ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_120),'#skF_5')
      | r1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_120) ) ),
    inference(resolution,[status(thm)],[c_98,c_52])).

tff(c_362,plain,(
    r1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_357])).

tff(c_424,plain,(
    r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_362])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( ~ r1_xboole_0(B_13,A_12)
      | ~ r1_tarski(B_13,A_12)
      | v1_xboole_0(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_444,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_424,c_16])).

tff(c_554,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_444])).

tff(c_557,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_554])).

tff(c_561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_263,c_557])).

tff(c_562,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_567,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_562,c_8])).

tff(c_200,plain,(
    ! [C_98,A_99,B_100] :
      ( v4_relat_1(C_98,A_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_223,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_200])).

tff(c_42,plain,(
    ! [B_34,A_33] :
      ( k7_relat_1(B_34,A_33) = B_34
      | ~ v4_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_227,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_223,c_42])).

tff(c_230,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_227])).

tff(c_36,plain,(
    ! [B_30,A_29] :
      ( k2_relat_1(k7_relat_1(B_30,A_29)) = k9_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_234,plain,
    ( k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_36])).

tff(c_238,plain,(
    k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_234])).

tff(c_578,plain,(
    k9_relat_1('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_238])).

tff(c_28,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(B_24),A_23)
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_370,plain,(
    ! [B_121,A_122] :
      ( r1_xboole_0(k1_relat_1(B_121),A_122)
      | k9_relat_1(B_121,A_122) != k1_xboole_0
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1229,plain,(
    ! [B_197,A_198] :
      ( ~ r1_tarski(k1_relat_1(B_197),A_198)
      | v1_xboole_0(k1_relat_1(B_197))
      | k9_relat_1(B_197,A_198) != k1_xboole_0
      | ~ v1_relat_1(B_197) ) ),
    inference(resolution,[status(thm)],[c_370,c_16])).

tff(c_1927,plain,(
    ! [B_287,A_288] :
      ( v1_xboole_0(k1_relat_1(B_287))
      | k9_relat_1(B_287,A_288) != k1_xboole_0
      | ~ v4_relat_1(B_287,A_288)
      | ~ v1_relat_1(B_287) ) ),
    inference(resolution,[status(thm)],[c_28,c_1229])).

tff(c_1931,plain,
    ( v1_xboole_0(k1_relat_1('#skF_6'))
    | k9_relat_1('#skF_6','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_223,c_1927])).

tff(c_1937,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_578,c_1931])).

tff(c_1941,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1937,c_8])).

tff(c_1945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_542,c_1941])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.77  
% 4.04/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.78  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.04/1.78  
% 4.04/1.78  %Foreground sorts:
% 4.04/1.78  
% 4.04/1.78  
% 4.04/1.78  %Background operators:
% 4.04/1.78  
% 4.04/1.78  
% 4.04/1.78  %Foreground operators:
% 4.04/1.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.04/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.04/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.04/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.04/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.04/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.04/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.04/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.04/1.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.04/1.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.04/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.04/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.04/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.04/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.04/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.04/1.78  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.04/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.04/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.04/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.04/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.04/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.04/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.04/1.78  
% 4.04/1.79  tff(f_147, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 4.04/1.79  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.04/1.79  tff(f_96, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.04/1.79  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.04/1.79  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.04/1.79  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.04/1.79  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.04/1.79  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.04/1.79  tff(f_69, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.04/1.79  tff(f_62, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.04/1.79  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.04/1.79  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.04/1.79  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.04/1.79  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.04/1.79  tff(f_106, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 4.04/1.79  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.04/1.79  tff(c_517, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.04/1.79  tff(c_540, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_517])).
% 4.04/1.79  tff(c_54, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.04/1.79  tff(c_542, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_540, c_54])).
% 4.04/1.79  tff(c_34, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.04/1.79  tff(c_109, plain, (![B_74, A_75]: (v1_relat_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.04/1.79  tff(c_112, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_109])).
% 4.04/1.79  tff(c_119, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_112])).
% 4.04/1.79  tff(c_240, plain, (![C_101, B_102, A_103]: (v5_relat_1(C_101, B_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.04/1.79  tff(c_263, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_240])).
% 4.04/1.79  tff(c_32, plain, (![B_26, A_25]: (r1_tarski(k2_relat_1(B_26), A_25) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.04/1.79  tff(c_399, plain, (![A_128, B_129, C_130]: (k2_relset_1(A_128, B_129, C_130)=k2_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.04/1.79  tff(c_422, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_399])).
% 4.04/1.79  tff(c_122, plain, (![A_77, B_78]: (r2_hidden('#skF_2'(A_77, B_78), B_78) | r1_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.04/1.79  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(A_16, B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.04/1.79  tff(c_131, plain, (![A_77, B_78]: (m1_subset_1('#skF_2'(A_77, B_78), B_78) | r1_xboole_0(A_77, B_78))), inference(resolution, [status(thm)], [c_122, c_20])).
% 4.04/1.79  tff(c_98, plain, (![A_70, B_71]: (r2_hidden('#skF_2'(A_70, B_71), A_70) | r1_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.04/1.79  tff(c_52, plain, (![D_55]: (~r2_hidden(D_55, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_55, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.04/1.79  tff(c_357, plain, (![B_120]: (~m1_subset_1('#skF_2'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_120), '#skF_5') | r1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_120))), inference(resolution, [status(thm)], [c_98, c_52])).
% 4.04/1.79  tff(c_362, plain, (r1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_131, c_357])).
% 4.04/1.79  tff(c_424, plain, (r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_422, c_362])).
% 4.04/1.79  tff(c_16, plain, (![B_13, A_12]: (~r1_xboole_0(B_13, A_12) | ~r1_tarski(B_13, A_12) | v1_xboole_0(B_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.04/1.79  tff(c_444, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_424, c_16])).
% 4.04/1.79  tff(c_554, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_444])).
% 4.04/1.79  tff(c_557, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_554])).
% 4.04/1.79  tff(c_561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_263, c_557])).
% 4.04/1.79  tff(c_562, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_444])).
% 4.04/1.79  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.04/1.79  tff(c_567, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_562, c_8])).
% 4.04/1.79  tff(c_200, plain, (![C_98, A_99, B_100]: (v4_relat_1(C_98, A_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.04/1.79  tff(c_223, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_200])).
% 4.04/1.79  tff(c_42, plain, (![B_34, A_33]: (k7_relat_1(B_34, A_33)=B_34 | ~v4_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.04/1.79  tff(c_227, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_223, c_42])).
% 4.04/1.79  tff(c_230, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_227])).
% 4.04/1.79  tff(c_36, plain, (![B_30, A_29]: (k2_relat_1(k7_relat_1(B_30, A_29))=k9_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.04/1.79  tff(c_234, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_230, c_36])).
% 4.04/1.79  tff(c_238, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_234])).
% 4.04/1.79  tff(c_578, plain, (k9_relat_1('#skF_6', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_567, c_238])).
% 4.04/1.79  tff(c_28, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(B_24), A_23) | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.04/1.79  tff(c_370, plain, (![B_121, A_122]: (r1_xboole_0(k1_relat_1(B_121), A_122) | k9_relat_1(B_121, A_122)!=k1_xboole_0 | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.04/1.79  tff(c_1229, plain, (![B_197, A_198]: (~r1_tarski(k1_relat_1(B_197), A_198) | v1_xboole_0(k1_relat_1(B_197)) | k9_relat_1(B_197, A_198)!=k1_xboole_0 | ~v1_relat_1(B_197))), inference(resolution, [status(thm)], [c_370, c_16])).
% 4.04/1.79  tff(c_1927, plain, (![B_287, A_288]: (v1_xboole_0(k1_relat_1(B_287)) | k9_relat_1(B_287, A_288)!=k1_xboole_0 | ~v4_relat_1(B_287, A_288) | ~v1_relat_1(B_287))), inference(resolution, [status(thm)], [c_28, c_1229])).
% 4.04/1.79  tff(c_1931, plain, (v1_xboole_0(k1_relat_1('#skF_6')) | k9_relat_1('#skF_6', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_223, c_1927])).
% 4.04/1.79  tff(c_1937, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_578, c_1931])).
% 4.04/1.79  tff(c_1941, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_1937, c_8])).
% 4.04/1.79  tff(c_1945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_542, c_1941])).
% 4.04/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.79  
% 4.04/1.79  Inference rules
% 4.04/1.79  ----------------------
% 4.04/1.79  #Ref     : 0
% 4.04/1.79  #Sup     : 393
% 4.04/1.79  #Fact    : 0
% 4.04/1.79  #Define  : 0
% 4.04/1.79  #Split   : 2
% 4.04/1.79  #Chain   : 0
% 4.04/1.79  #Close   : 0
% 4.04/1.79  
% 4.04/1.79  Ordering : KBO
% 4.04/1.79  
% 4.04/1.79  Simplification rules
% 4.04/1.79  ----------------------
% 4.04/1.79  #Subsume      : 101
% 4.04/1.79  #Demod        : 154
% 4.04/1.79  #Tautology    : 100
% 4.04/1.79  #SimpNegUnit  : 10
% 4.04/1.79  #BackRed      : 23
% 4.04/1.79  
% 4.04/1.79  #Partial instantiations: 0
% 4.04/1.79  #Strategies tried      : 1
% 4.04/1.79  
% 4.04/1.79  Timing (in seconds)
% 4.04/1.79  ----------------------
% 4.04/1.79  Preprocessing        : 0.34
% 4.04/1.79  Parsing              : 0.19
% 4.04/1.79  CNF conversion       : 0.02
% 4.04/1.79  Main loop            : 0.58
% 4.04/1.79  Inferencing          : 0.22
% 4.04/1.79  Reduction            : 0.16
% 4.04/1.79  Demodulation         : 0.11
% 4.04/1.79  BG Simplification    : 0.02
% 4.04/1.79  Subsumption          : 0.12
% 4.04/1.79  Abstraction          : 0.03
% 4.04/1.80  MUC search           : 0.00
% 4.04/1.80  Cooper               : 0.00
% 4.04/1.80  Total                : 0.95
% 4.04/1.80  Index Insertion      : 0.00
% 4.04/1.80  Index Deletion       : 0.00
% 4.04/1.80  Index Matching       : 0.00
% 4.04/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
