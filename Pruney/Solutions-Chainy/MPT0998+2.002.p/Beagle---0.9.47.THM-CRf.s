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
% DateTime   : Thu Dec  3 10:13:53 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 235 expanded)
%              Number of leaves         :   31 (  95 expanded)
%              Depth                    :    8
%              Number of atoms          :  171 ( 642 expanded)
%              Number of equality atoms :   46 ( 124 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( B != k1_xboole_0
         => ! [E] :
              ( r2_hidden(E,k8_relset_1(A,B,D,C))
            <=> ( r2_hidden(E,A)
                & r2_hidden(k1_funct_1(D,E),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_269,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k8_relset_1(A_110,B_111,C_112,D_113) = k10_relat_1(C_112,D_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_272,plain,(
    ! [D_113] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_113) = k10_relat_1('#skF_6',D_113) ),
    inference(resolution,[status(thm)],[c_42,c_269])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_60])).

tff(c_66,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_63])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_144,plain,(
    ! [A_66,D_67,B_68] :
      ( r2_hidden(k1_funct_1(A_66,D_67),B_68)
      | ~ r2_hidden(D_67,k10_relat_1(A_66,B_68))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,
    ( r2_hidden('#skF_7','#skF_3')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_8','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_68,plain,(
    ~ r2_hidden('#skF_8','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_69,plain,(
    ! [A_33,B_34,C_35] :
      ( k1_relset_1(A_33,B_34,C_35) = k1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_73,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_113,plain,(
    ! [B_54,A_55,C_56] :
      ( k1_xboole_0 = B_54
      | k1_relset_1(A_55,B_54,C_56) = A_55
      | ~ v1_funct_2(C_56,A_55,B_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_116,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_113])).

tff(c_119,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_73,c_116])).

tff(c_120,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_119])).

tff(c_81,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k8_relset_1(A_40,B_41,C_42,D_43) = k10_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_84,plain,(
    ! [D_43] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_43) = k10_relat_1('#skF_6',D_43) ),
    inference(resolution,[status(thm)],[c_42,c_81])).

tff(c_58,plain,
    ( r2_hidden('#skF_7','#skF_3')
    | r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_67,plain,(
    r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_85,plain,(
    r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_67])).

tff(c_10,plain,(
    ! [D_17,A_6,B_13] :
      ( r2_hidden(D_17,k1_relat_1(A_6))
      | ~ r2_hidden(D_17,k10_relat_1(A_6,B_13))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_99,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_85,c_10])).

tff(c_102,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_46,c_99])).

tff(c_121,plain,(
    r2_hidden('#skF_8','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_102])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_121])).

tff(c_125,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_127,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_151,plain,
    ( ~ r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_144,c_127])).

tff(c_155,plain,(
    ~ r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_46,c_151])).

tff(c_156,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k8_relset_1(A_69,B_70,C_71,D_72) = k10_relat_1(C_71,D_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_159,plain,(
    ! [D_72] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_72) = k10_relat_1('#skF_6',D_72) ),
    inference(resolution,[status(thm)],[c_42,c_156])).

tff(c_160,plain,(
    r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_67])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_160])).

tff(c_163,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_165,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_169,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_165])).

tff(c_218,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_221,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_218])).

tff(c_224,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_169,c_221])).

tff(c_225,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_224])).

tff(c_126,plain,(
    r2_hidden('#skF_8','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_164,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_179,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k8_relset_1(A_80,B_81,C_82,D_83) = k10_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_182,plain,(
    ! [D_83] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_83) = k10_relat_1('#skF_6',D_83) ),
    inference(resolution,[status(thm)],[c_42,c_179])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_7',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5'))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_8','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_202,plain,(
    ~ r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_164,c_182,c_48])).

tff(c_50,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_8','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_178,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_164,c_50])).

tff(c_226,plain,(
    ! [D_100,A_101,B_102] :
      ( r2_hidden(D_100,k10_relat_1(A_101,B_102))
      | ~ r2_hidden(k1_funct_1(A_101,D_100),B_102)
      | ~ r2_hidden(D_100,k1_relat_1(A_101))
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_232,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_178,c_226])).

tff(c_239,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_46,c_232])).

tff(c_240,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_239])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_225,c_240])).

tff(c_254,plain,(
    ~ r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_273,plain,(
    ~ r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_254])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_7',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5'))
    | r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_283,plain,
    ( ~ r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5'))
    | r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_272,c_54])).

tff(c_284,plain,(
    ~ r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_253,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_256,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_260,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_256])).

tff(c_295,plain,(
    ! [B_124,A_125,C_126] :
      ( k1_xboole_0 = B_124
      | k1_relset_1(A_125,B_124,C_126) = A_125
      | ~ v1_funct_2(C_126,A_125,B_124)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_298,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_295])).

tff(c_301,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_260,c_298])).

tff(c_302,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_301])).

tff(c_56,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5')
    | r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_265,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_56])).

tff(c_320,plain,(
    ! [D_130,A_131,B_132] :
      ( r2_hidden(D_130,k10_relat_1(A_131,B_132))
      | ~ r2_hidden(k1_funct_1(A_131,D_130),B_132)
      | ~ r2_hidden(D_130,k1_relat_1(A_131))
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_326,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_265,c_320])).

tff(c_330,plain,(
    r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_46,c_253,c_302,c_326])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_330])).

tff(c_333,plain,(
    r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n023.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:32:51 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  
% 2.21/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 2.21/1.28  
% 2.21/1.28  %Foreground sorts:
% 2.21/1.28  
% 2.21/1.28  
% 2.21/1.28  %Background operators:
% 2.21/1.28  
% 2.21/1.28  
% 2.21/1.28  %Foreground operators:
% 2.21/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.28  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.21/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.21/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.21/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.21/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.21/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.21/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.21/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.21/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.28  
% 2.21/1.30  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: (r2_hidden(E, k8_relset_1(A, B, D, C)) <=> (r2_hidden(E, A) & r2_hidden(k1_funct_1(D, E), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_funct_2)).
% 2.21/1.30  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.21/1.30  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.21/1.30  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.21/1.30  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 2.21/1.30  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.21/1.30  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.21/1.30  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.30  tff(c_269, plain, (![A_110, B_111, C_112, D_113]: (k8_relset_1(A_110, B_111, C_112, D_113)=k10_relat_1(C_112, D_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.30  tff(c_272, plain, (![D_113]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_113)=k10_relat_1('#skF_6', D_113))), inference(resolution, [status(thm)], [c_42, c_269])).
% 2.21/1.30  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.21/1.30  tff(c_60, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.30  tff(c_63, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_60])).
% 2.21/1.30  tff(c_66, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_63])).
% 2.21/1.30  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.30  tff(c_144, plain, (![A_66, D_67, B_68]: (r2_hidden(k1_funct_1(A_66, D_67), B_68) | ~r2_hidden(D_67, k10_relat_1(A_66, B_68)) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.21/1.30  tff(c_52, plain, (r2_hidden('#skF_7', '#skF_3') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_8', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.30  tff(c_68, plain, (~r2_hidden('#skF_8', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 2.21/1.30  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.30  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.30  tff(c_69, plain, (![A_33, B_34, C_35]: (k1_relset_1(A_33, B_34, C_35)=k1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.21/1.30  tff(c_73, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_69])).
% 2.21/1.30  tff(c_113, plain, (![B_54, A_55, C_56]: (k1_xboole_0=B_54 | k1_relset_1(A_55, B_54, C_56)=A_55 | ~v1_funct_2(C_56, A_55, B_54) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.30  tff(c_116, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_113])).
% 2.21/1.30  tff(c_119, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_73, c_116])).
% 2.21/1.30  tff(c_120, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40, c_119])).
% 2.21/1.30  tff(c_81, plain, (![A_40, B_41, C_42, D_43]: (k8_relset_1(A_40, B_41, C_42, D_43)=k10_relat_1(C_42, D_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.30  tff(c_84, plain, (![D_43]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_43)=k10_relat_1('#skF_6', D_43))), inference(resolution, [status(thm)], [c_42, c_81])).
% 2.21/1.30  tff(c_58, plain, (r2_hidden('#skF_7', '#skF_3') | r2_hidden('#skF_8', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.30  tff(c_67, plain, (r2_hidden('#skF_8', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_58])).
% 2.21/1.30  tff(c_85, plain, (r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_67])).
% 2.21/1.30  tff(c_10, plain, (![D_17, A_6, B_13]: (r2_hidden(D_17, k1_relat_1(A_6)) | ~r2_hidden(D_17, k10_relat_1(A_6, B_13)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.21/1.30  tff(c_99, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_85, c_10])).
% 2.21/1.30  tff(c_102, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_46, c_99])).
% 2.21/1.30  tff(c_121, plain, (r2_hidden('#skF_8', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_102])).
% 2.21/1.30  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_121])).
% 2.21/1.30  tff(c_125, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5') | r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 2.21/1.30  tff(c_127, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_125])).
% 2.21/1.30  tff(c_151, plain, (~r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_144, c_127])).
% 2.21/1.30  tff(c_155, plain, (~r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_46, c_151])).
% 2.21/1.30  tff(c_156, plain, (![A_69, B_70, C_71, D_72]: (k8_relset_1(A_69, B_70, C_71, D_72)=k10_relat_1(C_71, D_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.30  tff(c_159, plain, (![D_72]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_72)=k10_relat_1('#skF_6', D_72))), inference(resolution, [status(thm)], [c_42, c_156])).
% 2.21/1.30  tff(c_160, plain, (r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_67])).
% 2.21/1.30  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_160])).
% 2.21/1.30  tff(c_163, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_125])).
% 2.21/1.30  tff(c_165, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.21/1.30  tff(c_169, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_165])).
% 2.21/1.30  tff(c_218, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.30  tff(c_221, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_218])).
% 2.21/1.30  tff(c_224, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_169, c_221])).
% 2.21/1.30  tff(c_225, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40, c_224])).
% 2.21/1.30  tff(c_126, plain, (r2_hidden('#skF_8', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 2.21/1.30  tff(c_164, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_125])).
% 2.21/1.30  tff(c_179, plain, (![A_80, B_81, C_82, D_83]: (k8_relset_1(A_80, B_81, C_82, D_83)=k10_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.30  tff(c_182, plain, (![D_83]: (k8_relset_1('#skF_3', '#skF_4', '#skF_6', D_83)=k10_relat_1('#skF_6', D_83))), inference(resolution, [status(thm)], [c_42, c_179])).
% 2.21/1.30  tff(c_48, plain, (~r2_hidden('#skF_7', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5')) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_8', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.30  tff(c_202, plain, (~r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_164, c_182, c_48])).
% 2.21/1.30  tff(c_50, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), '#skF_5') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_8', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.30  tff(c_178, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_164, c_50])).
% 2.21/1.30  tff(c_226, plain, (![D_100, A_101, B_102]: (r2_hidden(D_100, k10_relat_1(A_101, B_102)) | ~r2_hidden(k1_funct_1(A_101, D_100), B_102) | ~r2_hidden(D_100, k1_relat_1(A_101)) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.21/1.30  tff(c_232, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_178, c_226])).
% 2.21/1.30  tff(c_239, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_46, c_232])).
% 2.21/1.30  tff(c_240, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_202, c_239])).
% 2.21/1.30  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_225, c_240])).
% 2.21/1.30  tff(c_254, plain, (~r2_hidden('#skF_8', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_58])).
% 2.21/1.30  tff(c_273, plain, (~r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_254])).
% 2.21/1.30  tff(c_54, plain, (~r2_hidden('#skF_7', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5')) | r2_hidden('#skF_8', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.30  tff(c_283, plain, (~r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5')) | r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_272, c_54])).
% 2.21/1.30  tff(c_284, plain, (~r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_283])).
% 2.21/1.30  tff(c_253, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 2.21/1.30  tff(c_256, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.21/1.30  tff(c_260, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_256])).
% 2.21/1.30  tff(c_295, plain, (![B_124, A_125, C_126]: (k1_xboole_0=B_124 | k1_relset_1(A_125, B_124, C_126)=A_125 | ~v1_funct_2(C_126, A_125, B_124) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.21/1.30  tff(c_298, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_295])).
% 2.21/1.30  tff(c_301, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_260, c_298])).
% 2.21/1.30  tff(c_302, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40, c_301])).
% 2.21/1.30  tff(c_56, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), '#skF_5') | r2_hidden('#skF_8', k8_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.21/1.30  tff(c_265, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_254, c_56])).
% 2.21/1.30  tff(c_320, plain, (![D_130, A_131, B_132]: (r2_hidden(D_130, k10_relat_1(A_131, B_132)) | ~r2_hidden(k1_funct_1(A_131, D_130), B_132) | ~r2_hidden(D_130, k1_relat_1(A_131)) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.21/1.30  tff(c_326, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5')) | ~r2_hidden('#skF_7', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_265, c_320])).
% 2.21/1.30  tff(c_330, plain, (r2_hidden('#skF_7', k10_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_46, c_253, c_302, c_326])).
% 2.21/1.30  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_330])).
% 2.21/1.30  tff(c_333, plain, (r2_hidden('#skF_8', k10_relat_1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_283])).
% 2.21/1.30  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_333])).
% 2.21/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.30  
% 2.21/1.30  Inference rules
% 2.21/1.30  ----------------------
% 2.21/1.30  #Ref     : 0
% 2.21/1.30  #Sup     : 46
% 2.21/1.30  #Fact    : 0
% 2.21/1.30  #Define  : 0
% 2.21/1.30  #Split   : 5
% 2.21/1.30  #Chain   : 0
% 2.21/1.30  #Close   : 0
% 2.21/1.30  
% 2.21/1.30  Ordering : KBO
% 2.21/1.30  
% 2.21/1.30  Simplification rules
% 2.21/1.30  ----------------------
% 2.21/1.30  #Subsume      : 4
% 2.21/1.30  #Demod        : 60
% 2.21/1.30  #Tautology    : 33
% 2.21/1.30  #SimpNegUnit  : 11
% 2.21/1.30  #BackRed      : 9
% 2.21/1.30  
% 2.21/1.30  #Partial instantiations: 0
% 2.21/1.30  #Strategies tried      : 1
% 2.21/1.30  
% 2.21/1.30  Timing (in seconds)
% 2.21/1.30  ----------------------
% 2.21/1.30  Preprocessing        : 0.32
% 2.21/1.30  Parsing              : 0.17
% 2.21/1.30  CNF conversion       : 0.02
% 2.21/1.30  Main loop            : 0.23
% 2.21/1.30  Inferencing          : 0.08
% 2.21/1.30  Reduction            : 0.07
% 2.21/1.30  Demodulation         : 0.05
% 2.21/1.30  BG Simplification    : 0.02
% 2.21/1.30  Subsumption          : 0.04
% 2.21/1.30  Abstraction          : 0.01
% 2.21/1.30  MUC search           : 0.00
% 2.21/1.30  Cooper               : 0.00
% 2.21/1.30  Total                : 0.60
% 2.21/1.30  Index Insertion      : 0.00
% 2.21/1.30  Index Deletion       : 0.00
% 2.21/1.30  Index Matching       : 0.00
% 2.21/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
