%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:19 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 465 expanded)
%              Number of leaves         :   33 ( 168 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 (1054 expanded)
%              Number of equality atoms :   26 ( 249 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_104,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_113,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_55,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_55])).

tff(c_65,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_61])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_133,plain,(
    ! [A_71,B_72,A_73] :
      ( m1_subset_1(A_71,B_72)
      | ~ r2_hidden(A_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_125])).

tff(c_136,plain,(
    ! [A_1,B_72] :
      ( m1_subset_1('#skF_1'(A_1),B_72)
      | ~ r1_tarski(A_1,B_72)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_2,c_133])).

tff(c_162,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_176,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_162])).

tff(c_49,plain,(
    ! [D_46] :
      ( ~ r2_hidden(D_46,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_46,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_189,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_176,c_54])).

tff(c_190,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_194,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136,c_190])).

tff(c_195,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_198,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_113,c_198])).

tff(c_203,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_204,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_237,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_204])).

tff(c_222,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_236,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_222])).

tff(c_30,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_250,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_30])).

tff(c_271,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_2'(A_85,B_86),k2_relat_1(B_86))
      | ~ r2_hidden(A_85,k1_relat_1(B_86))
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_276,plain,(
    ! [A_85] :
      ( r2_hidden('#skF_2'(A_85,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_85,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_271])).

tff(c_285,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_2'(A_88,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_88,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_276])).

tff(c_130,plain,(
    ! [A_67,B_4,A_3] :
      ( m1_subset_1(A_67,B_4)
      | ~ r2_hidden(A_67,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_125])).

tff(c_396,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1('#skF_2'(A_111,'#skF_5'),B_112)
      | ~ r1_tarski(k1_xboole_0,B_112)
      | ~ r2_hidden(A_111,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_285,c_130])).

tff(c_399,plain,(
    ! [B_112] :
      ( m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),B_112)
      | ~ r1_tarski(k1_xboole_0,B_112)
      | k1_relat_1('#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_396])).

tff(c_403,plain,(
    ! [B_113] :
      ( m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),B_113)
      | ~ r1_tarski(k1_xboole_0,B_113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_399])).

tff(c_28,plain,(
    ! [D_38] :
      ( ~ r2_hidden(D_38,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_38,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_177,plain,(
    ! [D_38] :
      ( ~ r2_hidden(D_38,k2_relat_1('#skF_5'))
      | ~ m1_subset_1(D_38,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_28])).

tff(c_206,plain,(
    ! [D_38] :
      ( ~ r2_hidden(D_38,k1_xboole_0)
      | ~ m1_subset_1(D_38,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_177])).

tff(c_293,plain,(
    ! [A_89] :
      ( ~ m1_subset_1('#skF_2'(A_89,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_89,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_285,c_206])).

tff(c_297,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_293])).

tff(c_300,plain,(
    ~ m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_297])).

tff(c_406,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_403,c_300])).

tff(c_437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_406])).

tff(c_438,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_439,plain,(
    m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_456,plain,(
    m1_subset_1('#skF_1'(k1_xboole_0),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_439])).

tff(c_182,plain,(
    ! [D_79] :
      ( ~ r2_hidden(D_79,k2_relat_1('#skF_5'))
      | ~ m1_subset_1(D_79,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_28])).

tff(c_187,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_182])).

tff(c_188,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_438,c_188])).

tff(c_463,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_485,plain,(
    ! [A_11] :
      ( r1_tarski(k1_xboole_0,A_11)
      | ~ v5_relat_1('#skF_5',A_11)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_14])).

tff(c_516,plain,(
    ! [A_119] :
      ( r1_tarski(k1_xboole_0,A_119)
      | ~ v5_relat_1('#skF_5',A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_485])).

tff(c_524,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_516])).

tff(c_465,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_479,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_465])).

tff(c_501,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_30])).

tff(c_529,plain,(
    ! [A_120,B_121] :
      ( r2_hidden('#skF_2'(A_120,B_121),k2_relat_1(B_121))
      | ~ r2_hidden(A_120,k1_relat_1(B_121))
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_534,plain,(
    ! [A_120] :
      ( r2_hidden('#skF_2'(A_120,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_120,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_529])).

tff(c_539,plain,(
    ! [A_122] :
      ( r2_hidden('#skF_2'(A_122,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_122,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_534])).

tff(c_641,plain,(
    ! [A_142,B_143] :
      ( m1_subset_1('#skF_2'(A_142,'#skF_5'),B_143)
      | ~ r1_tarski(k1_xboole_0,B_143)
      | ~ r2_hidden(A_142,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_539,c_130])).

tff(c_644,plain,(
    ! [B_143] :
      ( m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),B_143)
      | ~ r1_tarski(k1_xboole_0,B_143)
      | k1_relat_1('#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_641])).

tff(c_648,plain,(
    ! [B_144] :
      ( m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),B_144)
      | ~ r1_tarski(k1_xboole_0,B_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_644])).

tff(c_480,plain,(
    ! [D_38] :
      ( ~ r2_hidden(D_38,k1_xboole_0)
      | ~ m1_subset_1(D_38,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_177])).

tff(c_549,plain,(
    ! [A_123] :
      ( ~ m1_subset_1('#skF_2'(A_123,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_123,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_539,c_480])).

tff(c_553,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_549])).

tff(c_556,plain,(
    ~ m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_553])).

tff(c_651,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_648,c_556])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:31:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.37  
% 2.50/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.37  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.50/1.37  
% 2.50/1.37  %Foreground sorts:
% 2.50/1.37  
% 2.50/1.37  
% 2.50/1.37  %Background operators:
% 2.50/1.37  
% 2.50/1.37  
% 2.50/1.37  %Foreground operators:
% 2.50/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.50/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.50/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.50/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.50/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.50/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.37  
% 2.81/1.39  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.81/1.39  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.81/1.39  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.81/1.39  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.81/1.39  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.81/1.39  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.81/1.39  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.81/1.39  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.81/1.39  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.81/1.39  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.81/1.39  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 2.81/1.39  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.81/1.39  tff(c_104, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.39  tff(c_113, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_104])).
% 2.81/1.39  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.81/1.39  tff(c_55, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.39  tff(c_61, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_55])).
% 2.81/1.39  tff(c_65, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_61])).
% 2.81/1.39  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.81/1.39  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.39  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.39  tff(c_125, plain, (![A_67, C_68, B_69]: (m1_subset_1(A_67, C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.39  tff(c_133, plain, (![A_71, B_72, A_73]: (m1_subset_1(A_71, B_72) | ~r2_hidden(A_71, A_73) | ~r1_tarski(A_73, B_72))), inference(resolution, [status(thm)], [c_6, c_125])).
% 2.81/1.39  tff(c_136, plain, (![A_1, B_72]: (m1_subset_1('#skF_1'(A_1), B_72) | ~r1_tarski(A_1, B_72) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_2, c_133])).
% 2.81/1.39  tff(c_162, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.81/1.39  tff(c_176, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_162])).
% 2.81/1.39  tff(c_49, plain, (![D_46]: (~r2_hidden(D_46, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_46, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.81/1.39  tff(c_54, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_49])).
% 2.81/1.39  tff(c_189, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_176, c_176, c_54])).
% 2.81/1.39  tff(c_190, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_189])).
% 2.81/1.39  tff(c_194, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_136, c_190])).
% 2.81/1.39  tff(c_195, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_194])).
% 2.81/1.39  tff(c_198, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_195])).
% 2.81/1.39  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_113, c_198])).
% 2.81/1.39  tff(c_203, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_194])).
% 2.81/1.39  tff(c_204, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_194])).
% 2.81/1.39  tff(c_237, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_204])).
% 2.81/1.39  tff(c_222, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.39  tff(c_236, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_222])).
% 2.81/1.39  tff(c_30, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.81/1.39  tff(c_250, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_236, c_30])).
% 2.81/1.39  tff(c_271, plain, (![A_85, B_86]: (r2_hidden('#skF_2'(A_85, B_86), k2_relat_1(B_86)) | ~r2_hidden(A_85, k1_relat_1(B_86)) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.81/1.39  tff(c_276, plain, (![A_85]: (r2_hidden('#skF_2'(A_85, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_85, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_203, c_271])).
% 2.81/1.39  tff(c_285, plain, (![A_88]: (r2_hidden('#skF_2'(A_88, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_88, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_276])).
% 2.81/1.39  tff(c_130, plain, (![A_67, B_4, A_3]: (m1_subset_1(A_67, B_4) | ~r2_hidden(A_67, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_125])).
% 2.81/1.39  tff(c_396, plain, (![A_111, B_112]: (m1_subset_1('#skF_2'(A_111, '#skF_5'), B_112) | ~r1_tarski(k1_xboole_0, B_112) | ~r2_hidden(A_111, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_285, c_130])).
% 2.81/1.39  tff(c_399, plain, (![B_112]: (m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), B_112) | ~r1_tarski(k1_xboole_0, B_112) | k1_relat_1('#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_396])).
% 2.81/1.39  tff(c_403, plain, (![B_113]: (m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), B_113) | ~r1_tarski(k1_xboole_0, B_113))), inference(negUnitSimplification, [status(thm)], [c_250, c_399])).
% 2.81/1.39  tff(c_28, plain, (![D_38]: (~r2_hidden(D_38, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_38, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.81/1.39  tff(c_177, plain, (![D_38]: (~r2_hidden(D_38, k2_relat_1('#skF_5')) | ~m1_subset_1(D_38, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_28])).
% 2.81/1.39  tff(c_206, plain, (![D_38]: (~r2_hidden(D_38, k1_xboole_0) | ~m1_subset_1(D_38, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_177])).
% 2.81/1.39  tff(c_293, plain, (![A_89]: (~m1_subset_1('#skF_2'(A_89, '#skF_5'), '#skF_4') | ~r2_hidden(A_89, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_285, c_206])).
% 2.81/1.39  tff(c_297, plain, (~m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_293])).
% 2.81/1.39  tff(c_300, plain, (~m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_250, c_297])).
% 2.81/1.39  tff(c_406, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_403, c_300])).
% 2.81/1.39  tff(c_437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_237, c_406])).
% 2.81/1.39  tff(c_438, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_189])).
% 2.81/1.39  tff(c_439, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_189])).
% 2.81/1.39  tff(c_456, plain, (m1_subset_1('#skF_1'(k1_xboole_0), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_438, c_439])).
% 2.81/1.39  tff(c_182, plain, (![D_79]: (~r2_hidden(D_79, k2_relat_1('#skF_5')) | ~m1_subset_1(D_79, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_28])).
% 2.81/1.39  tff(c_187, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_182])).
% 2.81/1.39  tff(c_188, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_187])).
% 2.81/1.39  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_456, c_438, c_188])).
% 2.81/1.39  tff(c_463, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_187])).
% 2.81/1.39  tff(c_485, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11) | ~v5_relat_1('#skF_5', A_11) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_463, c_14])).
% 2.81/1.39  tff(c_516, plain, (![A_119]: (r1_tarski(k1_xboole_0, A_119) | ~v5_relat_1('#skF_5', A_119))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_485])).
% 2.81/1.39  tff(c_524, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_113, c_516])).
% 2.81/1.39  tff(c_465, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.39  tff(c_479, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_465])).
% 2.81/1.39  tff(c_501, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_479, c_30])).
% 2.81/1.39  tff(c_529, plain, (![A_120, B_121]: (r2_hidden('#skF_2'(A_120, B_121), k2_relat_1(B_121)) | ~r2_hidden(A_120, k1_relat_1(B_121)) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.81/1.39  tff(c_534, plain, (![A_120]: (r2_hidden('#skF_2'(A_120, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_120, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_463, c_529])).
% 2.81/1.39  tff(c_539, plain, (![A_122]: (r2_hidden('#skF_2'(A_122, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_122, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_534])).
% 2.81/1.39  tff(c_641, plain, (![A_142, B_143]: (m1_subset_1('#skF_2'(A_142, '#skF_5'), B_143) | ~r1_tarski(k1_xboole_0, B_143) | ~r2_hidden(A_142, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_539, c_130])).
% 2.81/1.39  tff(c_644, plain, (![B_143]: (m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), B_143) | ~r1_tarski(k1_xboole_0, B_143) | k1_relat_1('#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_641])).
% 2.81/1.39  tff(c_648, plain, (![B_144]: (m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), B_144) | ~r1_tarski(k1_xboole_0, B_144))), inference(negUnitSimplification, [status(thm)], [c_501, c_644])).
% 2.81/1.39  tff(c_480, plain, (![D_38]: (~r2_hidden(D_38, k1_xboole_0) | ~m1_subset_1(D_38, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_177])).
% 2.81/1.39  tff(c_549, plain, (![A_123]: (~m1_subset_1('#skF_2'(A_123, '#skF_5'), '#skF_4') | ~r2_hidden(A_123, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_539, c_480])).
% 2.81/1.39  tff(c_553, plain, (~m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_549])).
% 2.81/1.39  tff(c_556, plain, (~m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_501, c_553])).
% 2.81/1.39  tff(c_651, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_648, c_556])).
% 2.81/1.39  tff(c_682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_524, c_651])).
% 2.81/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.39  
% 2.81/1.39  Inference rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Ref     : 0
% 2.81/1.39  #Sup     : 129
% 2.81/1.39  #Fact    : 0
% 2.81/1.39  #Define  : 0
% 2.81/1.39  #Split   : 5
% 2.81/1.39  #Chain   : 0
% 2.81/1.39  #Close   : 0
% 2.81/1.39  
% 2.81/1.39  Ordering : KBO
% 2.81/1.39  
% 2.81/1.39  Simplification rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Subsume      : 11
% 2.81/1.39  #Demod        : 62
% 2.81/1.39  #Tautology    : 33
% 2.81/1.39  #SimpNegUnit  : 4
% 2.81/1.39  #BackRed      : 10
% 2.81/1.39  
% 2.81/1.39  #Partial instantiations: 0
% 2.81/1.39  #Strategies tried      : 1
% 2.81/1.39  
% 2.81/1.39  Timing (in seconds)
% 2.81/1.39  ----------------------
% 2.81/1.39  Preprocessing        : 0.30
% 2.81/1.39  Parsing              : 0.16
% 2.81/1.39  CNF conversion       : 0.02
% 2.81/1.39  Main loop            : 0.31
% 2.81/1.39  Inferencing          : 0.13
% 2.81/1.39  Reduction            : 0.09
% 2.81/1.39  Demodulation         : 0.06
% 2.81/1.39  BG Simplification    : 0.02
% 2.81/1.39  Subsumption          : 0.04
% 2.81/1.39  Abstraction          : 0.02
% 2.81/1.39  MUC search           : 0.00
% 2.81/1.39  Cooper               : 0.00
% 2.81/1.39  Total                : 0.65
% 2.81/1.39  Index Insertion      : 0.00
% 2.81/1.39  Index Deletion       : 0.00
% 2.81/1.39  Index Matching       : 0.00
% 2.81/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
