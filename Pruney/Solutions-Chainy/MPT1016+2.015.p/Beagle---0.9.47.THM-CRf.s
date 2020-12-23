%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:42 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 238 expanded)
%              Number of leaves         :   32 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  180 ( 787 expanded)
%              Number of equality atoms :   47 ( 201 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_32,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_54])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    ! [A_43] :
      ( '#skF_2'(A_43) != '#skF_1'(A_43)
      | v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_52])).

tff(c_66,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30,c_63])).

tff(c_86,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_90,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_95,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k1_relset_1(A_51,B_52,C_53),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_106,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_95])).

tff(c_110,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_106])).

tff(c_67,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_2'(A_44),k1_relat_1(A_44))
      | v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_120,plain,(
    ! [A_55,A_56] :
      ( r2_hidden('#skF_2'(A_55),A_56)
      | ~ m1_subset_1(k1_relat_1(A_55),k1_zfmisc_1(A_56))
      | v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_123,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_120])).

tff(c_126,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30,c_123])).

tff(c_127,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_126])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_funct_1(A_6,'#skF_2'(A_6)) = k1_funct_1(A_6,'#skF_1'(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    ! [D_33,C_32] :
      ( v2_funct_1('#skF_4')
      | D_33 = C_32
      | k1_funct_1('#skF_4',D_33) != k1_funct_1('#skF_4',C_32)
      | ~ r2_hidden(D_33,'#skF_3')
      | ~ r2_hidden(C_32,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_140,plain,(
    ! [D_57,C_58] :
      ( D_57 = C_58
      | k1_funct_1('#skF_4',D_57) != k1_funct_1('#skF_4',C_58)
      | ~ r2_hidden(D_57,'#skF_3')
      | ~ r2_hidden(C_58,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50])).

tff(c_146,plain,(
    ! [D_57] :
      ( D_57 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_57) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_57,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_151,plain,(
    ! [D_57] :
      ( D_57 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_57) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_57,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30,c_127,c_146])).

tff(c_152,plain,(
    ! [D_57] :
      ( D_57 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_57) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_57,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_151])).

tff(c_181,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_152])).

tff(c_182,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_181])).

tff(c_75,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_1'(A_45),k1_relat_1(A_45))
      | v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_198,plain,(
    ! [A_68,A_69] :
      ( r2_hidden('#skF_1'(A_68),A_69)
      | ~ m1_subset_1(k1_relat_1(A_68),k1_zfmisc_1(A_69))
      | v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_201,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_198])).

tff(c_204,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_30,c_201])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_182,c_204])).

tff(c_207,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_28,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_208,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_228,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_34])).

tff(c_38,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_212,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_38])).

tff(c_343,plain,(
    ! [D_112,C_113,B_114,A_115] :
      ( k1_funct_1(k2_funct_1(D_112),k1_funct_1(D_112,C_113)) = C_113
      | k1_xboole_0 = B_114
      | ~ r2_hidden(C_113,A_115)
      | ~ v2_funct_1(D_112)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114)))
      | ~ v1_funct_2(D_112,A_115,B_114)
      | ~ v1_funct_1(D_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_356,plain,(
    ! [D_116,B_117] :
      ( k1_funct_1(k2_funct_1(D_116),k1_funct_1(D_116,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_117
      | ~ v2_funct_1(D_116)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_117)))
      | ~ v1_funct_2(D_116,'#skF_3',B_117)
      | ~ v1_funct_1(D_116) ) ),
    inference(resolution,[status(thm)],[c_212,c_343])).

tff(c_361,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_356])).

tff(c_365,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_208,c_228,c_361])).

tff(c_366,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_380,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_2])).

tff(c_36,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_210,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_36])).

tff(c_213,plain,(
    ! [B_70,A_71] :
      ( ~ r1_tarski(B_70,A_71)
      | ~ r2_hidden(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_221,plain,(
    ~ r1_tarski('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_210,c_213])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_221])).

tff(c_391,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_392,plain,(
    ! [D_120,B_121] :
      ( k1_funct_1(k2_funct_1(D_120),k1_funct_1(D_120,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_121
      | ~ v2_funct_1(D_120)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_121)))
      | ~ v1_funct_2(D_120,'#skF_3',B_121)
      | ~ v1_funct_1(D_120) ) ),
    inference(resolution,[status(thm)],[c_210,c_343])).

tff(c_397,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_392])).

tff(c_401,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_208,c_397])).

tff(c_402,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_401])).

tff(c_390,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_411,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_390])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.34  
% 2.54/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.34  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.54/1.34  
% 2.54/1.34  %Foreground sorts:
% 2.54/1.34  
% 2.54/1.34  
% 2.54/1.34  %Background operators:
% 2.54/1.34  
% 2.54/1.34  
% 2.54/1.34  %Foreground operators:
% 2.54/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.54/1.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.54/1.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.54/1.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.54/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.54/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.54/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.34  
% 2.54/1.36  tff(f_98, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 2.54/1.36  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.54/1.36  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 2.54/1.36  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.54/1.36  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.54/1.36  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.54/1.36  tff(f_80, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.54/1.36  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.54/1.36  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.54/1.36  tff(c_32, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.54/1.36  tff(c_52, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_32])).
% 2.54/1.36  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.54/1.36  tff(c_54, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.54/1.36  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_54])).
% 2.54/1.36  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.54/1.36  tff(c_60, plain, (![A_43]: ('#skF_2'(A_43)!='#skF_1'(A_43) | v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.36  tff(c_63, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_52])).
% 2.54/1.36  tff(c_66, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30, c_63])).
% 2.54/1.36  tff(c_86, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.54/1.36  tff(c_90, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_86])).
% 2.54/1.36  tff(c_95, plain, (![A_51, B_52, C_53]: (m1_subset_1(k1_relset_1(A_51, B_52, C_53), k1_zfmisc_1(A_51)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.54/1.36  tff(c_106, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_95])).
% 2.54/1.36  tff(c_110, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_106])).
% 2.54/1.36  tff(c_67, plain, (![A_44]: (r2_hidden('#skF_2'(A_44), k1_relat_1(A_44)) | v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.36  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.54/1.36  tff(c_120, plain, (![A_55, A_56]: (r2_hidden('#skF_2'(A_55), A_56) | ~m1_subset_1(k1_relat_1(A_55), k1_zfmisc_1(A_56)) | v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(resolution, [status(thm)], [c_67, c_4])).
% 2.54/1.36  tff(c_123, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_110, c_120])).
% 2.54/1.36  tff(c_126, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30, c_123])).
% 2.54/1.36  tff(c_127, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_126])).
% 2.54/1.36  tff(c_10, plain, (![A_6]: (k1_funct_1(A_6, '#skF_2'(A_6))=k1_funct_1(A_6, '#skF_1'(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.36  tff(c_50, plain, (![D_33, C_32]: (v2_funct_1('#skF_4') | D_33=C_32 | k1_funct_1('#skF_4', D_33)!=k1_funct_1('#skF_4', C_32) | ~r2_hidden(D_33, '#skF_3') | ~r2_hidden(C_32, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.54/1.36  tff(c_140, plain, (![D_57, C_58]: (D_57=C_58 | k1_funct_1('#skF_4', D_57)!=k1_funct_1('#skF_4', C_58) | ~r2_hidden(D_57, '#skF_3') | ~r2_hidden(C_58, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_50])).
% 2.54/1.36  tff(c_146, plain, (![D_57]: (D_57='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_57)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_57, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_140])).
% 2.54/1.36  tff(c_151, plain, (![D_57]: (D_57='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_57)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_57, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30, c_127, c_146])).
% 2.54/1.36  tff(c_152, plain, (![D_57]: (D_57='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_57)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_57, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_151])).
% 2.54/1.36  tff(c_181, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_152])).
% 2.54/1.36  tff(c_182, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_181])).
% 2.54/1.36  tff(c_75, plain, (![A_45]: (r2_hidden('#skF_1'(A_45), k1_relat_1(A_45)) | v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.54/1.36  tff(c_198, plain, (![A_68, A_69]: (r2_hidden('#skF_1'(A_68), A_69) | ~m1_subset_1(k1_relat_1(A_68), k1_zfmisc_1(A_69)) | v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_75, c_4])).
% 2.54/1.36  tff(c_201, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_110, c_198])).
% 2.54/1.36  tff(c_204, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_30, c_201])).
% 2.54/1.36  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_182, c_204])).
% 2.54/1.36  tff(c_207, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 2.54/1.36  tff(c_28, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.54/1.36  tff(c_208, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 2.54/1.36  tff(c_34, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.54/1.36  tff(c_228, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_34])).
% 2.54/1.36  tff(c_38, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.54/1.36  tff(c_212, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_38])).
% 2.54/1.36  tff(c_343, plain, (![D_112, C_113, B_114, A_115]: (k1_funct_1(k2_funct_1(D_112), k1_funct_1(D_112, C_113))=C_113 | k1_xboole_0=B_114 | ~r2_hidden(C_113, A_115) | ~v2_funct_1(D_112) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))) | ~v1_funct_2(D_112, A_115, B_114) | ~v1_funct_1(D_112))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.54/1.36  tff(c_356, plain, (![D_116, B_117]: (k1_funct_1(k2_funct_1(D_116), k1_funct_1(D_116, '#skF_5'))='#skF_5' | k1_xboole_0=B_117 | ~v2_funct_1(D_116) | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_117))) | ~v1_funct_2(D_116, '#skF_3', B_117) | ~v1_funct_1(D_116))), inference(resolution, [status(thm)], [c_212, c_343])).
% 2.54/1.36  tff(c_361, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_356])).
% 2.54/1.36  tff(c_365, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_208, c_228, c_361])).
% 2.54/1.36  tff(c_366, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_365])).
% 2.54/1.36  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.54/1.36  tff(c_380, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_2])).
% 2.54/1.36  tff(c_36, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.54/1.36  tff(c_210, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_36])).
% 2.54/1.36  tff(c_213, plain, (![B_70, A_71]: (~r1_tarski(B_70, A_71) | ~r2_hidden(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.54/1.36  tff(c_221, plain, (~r1_tarski('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_210, c_213])).
% 2.54/1.36  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_380, c_221])).
% 2.54/1.36  tff(c_391, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_365])).
% 2.54/1.36  tff(c_392, plain, (![D_120, B_121]: (k1_funct_1(k2_funct_1(D_120), k1_funct_1(D_120, '#skF_6'))='#skF_6' | k1_xboole_0=B_121 | ~v2_funct_1(D_120) | ~m1_subset_1(D_120, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_121))) | ~v1_funct_2(D_120, '#skF_3', B_121) | ~v1_funct_1(D_120))), inference(resolution, [status(thm)], [c_210, c_343])).
% 2.54/1.36  tff(c_397, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_392])).
% 2.54/1.36  tff(c_401, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_208, c_397])).
% 2.54/1.36  tff(c_402, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_391, c_401])).
% 2.54/1.36  tff(c_390, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_365])).
% 2.54/1.36  tff(c_411, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_402, c_390])).
% 2.54/1.36  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_411])).
% 2.54/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  Inference rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Ref     : 3
% 2.54/1.36  #Sup     : 71
% 2.54/1.36  #Fact    : 0
% 2.54/1.36  #Define  : 0
% 2.54/1.36  #Split   : 5
% 2.54/1.36  #Chain   : 0
% 2.54/1.36  #Close   : 0
% 2.54/1.36  
% 2.54/1.36  Ordering : KBO
% 2.54/1.36  
% 2.54/1.36  Simplification rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Subsume      : 8
% 2.54/1.36  #Demod        : 54
% 2.54/1.36  #Tautology    : 27
% 2.54/1.36  #SimpNegUnit  : 9
% 2.54/1.36  #BackRed      : 7
% 2.54/1.36  
% 2.54/1.36  #Partial instantiations: 0
% 2.54/1.36  #Strategies tried      : 1
% 2.54/1.36  
% 2.54/1.36  Timing (in seconds)
% 2.54/1.36  ----------------------
% 2.54/1.36  Preprocessing        : 0.31
% 2.54/1.36  Parsing              : 0.16
% 2.54/1.36  CNF conversion       : 0.02
% 2.54/1.36  Main loop            : 0.27
% 2.54/1.36  Inferencing          : 0.10
% 2.54/1.36  Reduction            : 0.08
% 2.54/1.36  Demodulation         : 0.05
% 2.54/1.36  BG Simplification    : 0.02
% 2.54/1.36  Subsumption          : 0.04
% 2.54/1.36  Abstraction          : 0.02
% 2.54/1.36  MUC search           : 0.00
% 2.54/1.36  Cooper               : 0.00
% 2.54/1.36  Total                : 0.62
% 2.54/1.36  Index Insertion      : 0.00
% 2.54/1.36  Index Deletion       : 0.00
% 2.54/1.36  Index Matching       : 0.00
% 2.54/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
