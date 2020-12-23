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
% DateTime   : Thu Dec  3 10:18:08 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 344 expanded)
%              Number of leaves         :   35 ( 134 expanded)
%              Depth                    :   22
%              Number of atoms          :  204 (1217 expanded)
%              Number of equality atoms :   15 (  54 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_18,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_65,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_65])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_71])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_162,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_171,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_162])).

tff(c_40,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_172,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_40])).

tff(c_179,plain,
    ( ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_172])).

tff(c_182,plain,(
    ~ v5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_179])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_129,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_138,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_129])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_201,plain,(
    ! [C_86,B_87] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_86),B_87,C_86),k1_relat_1(C_86))
      | v1_funct_2(C_86,k1_relat_1(C_86),B_87)
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_155,plain,(
    ! [A_72,C_73,B_74] :
      ( m1_subset_1(A_72,C_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(C_73))
      | ~ r2_hidden(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    ! [A_72,B_2,A_1] :
      ( m1_subset_1(A_72,B_2)
      | ~ r2_hidden(A_72,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_155])).

tff(c_204,plain,(
    ! [C_86,B_87,B_2] :
      ( m1_subset_1('#skF_1'(k1_relat_1(C_86),B_87,C_86),B_2)
      | ~ r1_tarski(k1_relat_1(C_86),B_2)
      | v1_funct_2(C_86,k1_relat_1(C_86),B_87)
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_201,c_160])).

tff(c_475,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k3_funct_2(A_150,B_151,C_152,D_153) = k1_funct_1(C_152,D_153)
      | ~ m1_subset_1(D_153,A_150)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ v1_funct_2(C_152,A_150,B_151)
      | ~ v1_funct_1(C_152)
      | v1_xboole_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1392,plain,(
    ! [B_497,C_499,C_495,B_496,B_498] :
      ( k3_funct_2(B_498,B_497,C_499,'#skF_1'(k1_relat_1(C_495),B_496,C_495)) = k1_funct_1(C_499,'#skF_1'(k1_relat_1(C_495),B_496,C_495))
      | ~ m1_subset_1(C_499,k1_zfmisc_1(k2_zfmisc_1(B_498,B_497)))
      | ~ v1_funct_2(C_499,B_498,B_497)
      | ~ v1_funct_1(C_499)
      | v1_xboole_0(B_498)
      | ~ r1_tarski(k1_relat_1(C_495),B_498)
      | v1_funct_2(C_495,k1_relat_1(C_495),B_496)
      | ~ v1_funct_1(C_495)
      | ~ v1_relat_1(C_495) ) ),
    inference(resolution,[status(thm)],[c_204,c_475])).

tff(c_1434,plain,(
    ! [C_495,B_496] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_495),B_496,C_495)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_495),B_496,C_495))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski(k1_relat_1(C_495),'#skF_3')
      | v1_funct_2(C_495,k1_relat_1(C_495),B_496)
      | ~ v1_funct_1(C_495)
      | ~ v1_relat_1(C_495) ) ),
    inference(resolution,[status(thm)],[c_44,c_1392])).

tff(c_1451,plain,(
    ! [C_495,B_496] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_495),B_496,C_495)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_495),B_496,C_495))
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski(k1_relat_1(C_495),'#skF_3')
      | v1_funct_2(C_495,k1_relat_1(C_495),B_496)
      | ~ v1_funct_1(C_495)
      | ~ v1_relat_1(C_495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1434])).

tff(c_1453,plain,(
    ! [C_500,B_501] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_500),B_501,C_500)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_500),B_501,C_500))
      | ~ r1_tarski(k1_relat_1(C_500),'#skF_3')
      | v1_funct_2(C_500,k1_relat_1(C_500),B_501)
      | ~ v1_funct_1(C_500)
      | ~ v1_relat_1(C_500) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1451])).

tff(c_42,plain,(
    ! [E_40] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_40),'#skF_2')
      | ~ m1_subset_1(E_40,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1481,plain,(
    ! [C_502,B_503] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_502),B_503,C_502)),'#skF_2')
      | ~ m1_subset_1('#skF_1'(k1_relat_1(C_502),B_503,C_502),'#skF_3')
      | ~ r1_tarski(k1_relat_1(C_502),'#skF_3')
      | v1_funct_2(C_502,k1_relat_1(C_502),B_503)
      | ~ v1_funct_1(C_502)
      | ~ v1_relat_1(C_502) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1453,c_42])).

tff(c_32,plain,(
    ! [C_27,B_26] :
      ( ~ r2_hidden(k1_funct_1(C_27,'#skF_1'(k1_relat_1(C_27),B_26,C_27)),B_26)
      | v1_funct_2(C_27,k1_relat_1(C_27),B_26)
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1489,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1481,c_32])).

tff(c_1497,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_48,c_1489])).

tff(c_1499,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1497])).

tff(c_1547,plain,
    ( ~ v4_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_1499])).

tff(c_1551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_138,c_1547])).

tff(c_1553,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1497])).

tff(c_283,plain,(
    ! [C_122,B_123] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_122),B_123,C_122),k1_relat_1(C_122))
      | m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_122),B_123)))
      | ~ v1_funct_1(C_122)
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_340,plain,(
    ! [C_138,B_139,B_140] :
      ( m1_subset_1('#skF_1'(k1_relat_1(C_138),B_139,C_138),B_140)
      | ~ r1_tarski(k1_relat_1(C_138),B_140)
      | m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_138),B_139)))
      | ~ v1_funct_1(C_138)
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_283,c_160])).

tff(c_20,plain,(
    ! [C_17,B_16,A_15] :
      ( v5_relat_1(C_17,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_390,plain,(
    ! [C_138,B_139,B_140] :
      ( v5_relat_1(C_138,B_139)
      | m1_subset_1('#skF_1'(k1_relat_1(C_138),B_139,C_138),B_140)
      | ~ r1_tarski(k1_relat_1(C_138),B_140)
      | ~ v1_funct_1(C_138)
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_340,c_20])).

tff(c_1552,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1497])).

tff(c_1564,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1552])).

tff(c_1580,plain,
    ( v5_relat_1('#skF_5','#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_390,c_1564])).

tff(c_1599,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_48,c_1553,c_1580])).

tff(c_1601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_1599])).

tff(c_1603,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1552])).

tff(c_26,plain,(
    ! [A_21,B_22,C_23,D_24] :
      ( k3_funct_2(A_21,B_22,C_23,D_24) = k1_funct_1(C_23,D_24)
      | ~ m1_subset_1(D_24,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1666,plain,(
    ! [B_22,C_23] :
      ( k3_funct_2('#skF_3',B_22,C_23,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1(C_23,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_22)))
      | ~ v1_funct_2(C_23,'#skF_3',B_22)
      | ~ v1_funct_1(C_23)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1603,c_26])).

tff(c_1672,plain,(
    ! [B_512,C_513] :
      ( k3_funct_2('#skF_3',B_512,C_513,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1(C_513,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_512)))
      | ~ v1_funct_2(C_513,'#skF_3',B_512)
      | ~ v1_funct_1(C_513) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1666])).

tff(c_1723,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1672])).

tff(c_1738,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1723])).

tff(c_1799,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1738,c_42])).

tff(c_1821,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1603,c_1799])).

tff(c_28,plain,(
    ! [C_27,B_26] :
      ( ~ r2_hidden(k1_funct_1(C_27,'#skF_1'(k1_relat_1(C_27),B_26,C_27)),B_26)
      | m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_27),B_26)))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1828,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1821,c_28])).

tff(c_1836,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_48,c_1828])).

tff(c_1859,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_1836,c_20])).

tff(c_1882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_1859])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.26/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/1.99  
% 5.26/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/1.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.26/1.99  
% 5.26/1.99  %Foreground sorts:
% 5.26/1.99  
% 5.26/1.99  
% 5.26/1.99  %Background operators:
% 5.26/1.99  
% 5.26/1.99  
% 5.26/1.99  %Foreground operators:
% 5.26/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.26/1.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.26/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.26/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.26/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.26/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.26/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.26/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.26/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.26/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.26/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.26/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.26/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.26/1.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.26/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.26/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.26/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.26/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.26/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.26/1.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.26/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.26/1.99  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 5.26/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.26/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.26/1.99  
% 5.26/2.01  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.26/2.01  tff(f_118, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 5.26/2.01  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.26/2.01  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.26/2.01  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.26/2.01  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.26/2.01  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.26/2.01  tff(f_96, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 5.26/2.01  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.26/2.01  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.26/2.01  tff(f_79, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.26/2.01  tff(c_18, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.26/2.01  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.26/2.01  tff(c_65, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.26/2.01  tff(c_71, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_65])).
% 5.26/2.01  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_71])).
% 5.26/2.01  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.26/2.01  tff(c_162, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.26/2.01  tff(c_171, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_162])).
% 5.26/2.01  tff(c_40, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.26/2.01  tff(c_172, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_40])).
% 5.26/2.01  tff(c_179, plain, (~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_172])).
% 5.26/2.01  tff(c_182, plain, (~v5_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_179])).
% 5.26/2.01  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.26/2.01  tff(c_129, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.26/2.01  tff(c_138, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_129])).
% 5.26/2.01  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.26/2.01  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.26/2.01  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.26/2.01  tff(c_201, plain, (![C_86, B_87]: (r2_hidden('#skF_1'(k1_relat_1(C_86), B_87, C_86), k1_relat_1(C_86)) | v1_funct_2(C_86, k1_relat_1(C_86), B_87) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.26/2.01  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.26/2.01  tff(c_155, plain, (![A_72, C_73, B_74]: (m1_subset_1(A_72, C_73) | ~m1_subset_1(B_74, k1_zfmisc_1(C_73)) | ~r2_hidden(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.26/2.01  tff(c_160, plain, (![A_72, B_2, A_1]: (m1_subset_1(A_72, B_2) | ~r2_hidden(A_72, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_155])).
% 5.26/2.01  tff(c_204, plain, (![C_86, B_87, B_2]: (m1_subset_1('#skF_1'(k1_relat_1(C_86), B_87, C_86), B_2) | ~r1_tarski(k1_relat_1(C_86), B_2) | v1_funct_2(C_86, k1_relat_1(C_86), B_87) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_201, c_160])).
% 5.26/2.01  tff(c_475, plain, (![A_150, B_151, C_152, D_153]: (k3_funct_2(A_150, B_151, C_152, D_153)=k1_funct_1(C_152, D_153) | ~m1_subset_1(D_153, A_150) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~v1_funct_2(C_152, A_150, B_151) | ~v1_funct_1(C_152) | v1_xboole_0(A_150))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.26/2.01  tff(c_1392, plain, (![B_497, C_499, C_495, B_496, B_498]: (k3_funct_2(B_498, B_497, C_499, '#skF_1'(k1_relat_1(C_495), B_496, C_495))=k1_funct_1(C_499, '#skF_1'(k1_relat_1(C_495), B_496, C_495)) | ~m1_subset_1(C_499, k1_zfmisc_1(k2_zfmisc_1(B_498, B_497))) | ~v1_funct_2(C_499, B_498, B_497) | ~v1_funct_1(C_499) | v1_xboole_0(B_498) | ~r1_tarski(k1_relat_1(C_495), B_498) | v1_funct_2(C_495, k1_relat_1(C_495), B_496) | ~v1_funct_1(C_495) | ~v1_relat_1(C_495))), inference(resolution, [status(thm)], [c_204, c_475])).
% 5.26/2.01  tff(c_1434, plain, (![C_495, B_496]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_495), B_496, C_495))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_495), B_496, C_495)) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~r1_tarski(k1_relat_1(C_495), '#skF_3') | v1_funct_2(C_495, k1_relat_1(C_495), B_496) | ~v1_funct_1(C_495) | ~v1_relat_1(C_495))), inference(resolution, [status(thm)], [c_44, c_1392])).
% 5.26/2.01  tff(c_1451, plain, (![C_495, B_496]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_495), B_496, C_495))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_495), B_496, C_495)) | v1_xboole_0('#skF_3') | ~r1_tarski(k1_relat_1(C_495), '#skF_3') | v1_funct_2(C_495, k1_relat_1(C_495), B_496) | ~v1_funct_1(C_495) | ~v1_relat_1(C_495))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1434])).
% 5.26/2.01  tff(c_1453, plain, (![C_500, B_501]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_500), B_501, C_500))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_500), B_501, C_500)) | ~r1_tarski(k1_relat_1(C_500), '#skF_3') | v1_funct_2(C_500, k1_relat_1(C_500), B_501) | ~v1_funct_1(C_500) | ~v1_relat_1(C_500))), inference(negUnitSimplification, [status(thm)], [c_52, c_1451])).
% 5.26/2.01  tff(c_42, plain, (![E_40]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_40), '#skF_2') | ~m1_subset_1(E_40, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.26/2.01  tff(c_1481, plain, (![C_502, B_503]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_502), B_503, C_502)), '#skF_2') | ~m1_subset_1('#skF_1'(k1_relat_1(C_502), B_503, C_502), '#skF_3') | ~r1_tarski(k1_relat_1(C_502), '#skF_3') | v1_funct_2(C_502, k1_relat_1(C_502), B_503) | ~v1_funct_1(C_502) | ~v1_relat_1(C_502))), inference(superposition, [status(thm), theory('equality')], [c_1453, c_42])).
% 5.26/2.01  tff(c_32, plain, (![C_27, B_26]: (~r2_hidden(k1_funct_1(C_27, '#skF_1'(k1_relat_1(C_27), B_26, C_27)), B_26) | v1_funct_2(C_27, k1_relat_1(C_27), B_26) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.26/2.01  tff(c_1489, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1481, c_32])).
% 5.26/2.01  tff(c_1497, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_48, c_1489])).
% 5.26/2.01  tff(c_1499, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1497])).
% 5.26/2.01  tff(c_1547, plain, (~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_1499])).
% 5.26/2.01  tff(c_1551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_138, c_1547])).
% 5.26/2.01  tff(c_1553, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_1497])).
% 5.26/2.01  tff(c_283, plain, (![C_122, B_123]: (r2_hidden('#skF_1'(k1_relat_1(C_122), B_123, C_122), k1_relat_1(C_122)) | m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_122), B_123))) | ~v1_funct_1(C_122) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.26/2.01  tff(c_340, plain, (![C_138, B_139, B_140]: (m1_subset_1('#skF_1'(k1_relat_1(C_138), B_139, C_138), B_140) | ~r1_tarski(k1_relat_1(C_138), B_140) | m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_138), B_139))) | ~v1_funct_1(C_138) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_283, c_160])).
% 5.26/2.01  tff(c_20, plain, (![C_17, B_16, A_15]: (v5_relat_1(C_17, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.26/2.01  tff(c_390, plain, (![C_138, B_139, B_140]: (v5_relat_1(C_138, B_139) | m1_subset_1('#skF_1'(k1_relat_1(C_138), B_139, C_138), B_140) | ~r1_tarski(k1_relat_1(C_138), B_140) | ~v1_funct_1(C_138) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_340, c_20])).
% 5.26/2.01  tff(c_1552, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_1497])).
% 5.26/2.01  tff(c_1564, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1552])).
% 5.26/2.01  tff(c_1580, plain, (v5_relat_1('#skF_5', '#skF_2') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_390, c_1564])).
% 5.26/2.01  tff(c_1599, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_48, c_1553, c_1580])).
% 5.26/2.01  tff(c_1601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_1599])).
% 5.26/2.01  tff(c_1603, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_1552])).
% 5.26/2.01  tff(c_26, plain, (![A_21, B_22, C_23, D_24]: (k3_funct_2(A_21, B_22, C_23, D_24)=k1_funct_1(C_23, D_24) | ~m1_subset_1(D_24, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.26/2.01  tff(c_1666, plain, (![B_22, C_23]: (k3_funct_2('#skF_3', B_22, C_23, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1(C_23, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_22))) | ~v1_funct_2(C_23, '#skF_3', B_22) | ~v1_funct_1(C_23) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_1603, c_26])).
% 5.26/2.01  tff(c_1672, plain, (![B_512, C_513]: (k3_funct_2('#skF_3', B_512, C_513, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1(C_513, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_512))) | ~v1_funct_2(C_513, '#skF_3', B_512) | ~v1_funct_1(C_513))), inference(negUnitSimplification, [status(thm)], [c_52, c_1666])).
% 5.26/2.01  tff(c_1723, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_1672])).
% 5.26/2.01  tff(c_1738, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1723])).
% 5.26/2.01  tff(c_1799, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1738, c_42])).
% 5.26/2.01  tff(c_1821, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1603, c_1799])).
% 5.26/2.01  tff(c_28, plain, (![C_27, B_26]: (~r2_hidden(k1_funct_1(C_27, '#skF_1'(k1_relat_1(C_27), B_26, C_27)), B_26) | m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_27), B_26))) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.26/2.01  tff(c_1828, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1821, c_28])).
% 5.26/2.01  tff(c_1836, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_48, c_1828])).
% 5.26/2.01  tff(c_1859, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_1836, c_20])).
% 5.26/2.01  tff(c_1882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_1859])).
% 5.26/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/2.01  
% 5.26/2.01  Inference rules
% 5.26/2.01  ----------------------
% 5.26/2.01  #Ref     : 0
% 5.26/2.01  #Sup     : 383
% 5.26/2.01  #Fact    : 2
% 5.26/2.01  #Define  : 0
% 5.26/2.01  #Split   : 8
% 5.26/2.01  #Chain   : 0
% 5.26/2.01  #Close   : 0
% 5.26/2.01  
% 5.26/2.01  Ordering : KBO
% 5.26/2.01  
% 5.26/2.01  Simplification rules
% 5.26/2.01  ----------------------
% 5.26/2.01  #Subsume      : 45
% 5.26/2.01  #Demod        : 81
% 5.26/2.01  #Tautology    : 30
% 5.26/2.01  #SimpNegUnit  : 7
% 5.26/2.01  #BackRed      : 1
% 5.26/2.01  
% 5.26/2.01  #Partial instantiations: 0
% 5.26/2.01  #Strategies tried      : 1
% 5.26/2.01  
% 5.26/2.01  Timing (in seconds)
% 5.26/2.01  ----------------------
% 5.26/2.01  Preprocessing        : 0.32
% 5.26/2.01  Parsing              : 0.17
% 5.26/2.01  CNF conversion       : 0.02
% 5.26/2.01  Main loop            : 0.87
% 5.26/2.01  Inferencing          : 0.32
% 5.26/2.01  Reduction            : 0.21
% 5.26/2.01  Demodulation         : 0.14
% 5.26/2.01  BG Simplification    : 0.04
% 5.26/2.01  Subsumption          : 0.22
% 5.26/2.01  Abstraction          : 0.05
% 5.26/2.01  MUC search           : 0.00
% 5.26/2.01  Cooper               : 0.00
% 5.26/2.01  Total                : 1.23
% 5.26/2.01  Index Insertion      : 0.00
% 5.26/2.01  Index Deletion       : 0.00
% 5.26/2.01  Index Matching       : 0.00
% 5.26/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
