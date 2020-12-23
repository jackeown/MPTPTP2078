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

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 252 expanded)
%              Number of leaves         :   40 ( 104 expanded)
%              Depth                    :   10
%              Number of atoms          :  212 ( 675 expanded)
%              Number of equality atoms :   51 ( 119 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_117,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_22,plain,(
    ! [A_46,B_47] : v1_relat_1(k2_zfmisc_1(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_78,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_78])).

tff(c_84,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_81])).

tff(c_509,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k8_relset_1(A_161,B_162,C_163,D_164) = k10_relat_1(C_163,D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_512,plain,(
    ! [D_164] : k8_relset_1('#skF_6','#skF_7','#skF_9',D_164) = k10_relat_1('#skF_9',D_164) ),
    inference(resolution,[status(thm)],[c_60,c_509])).

tff(c_76,plain,
    ( r2_hidden('#skF_10','#skF_6')
    | r2_hidden('#skF_11',k8_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_85,plain,(
    r2_hidden('#skF_11',k8_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_514,plain,(
    r2_hidden('#skF_11',k10_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_85])).

tff(c_26,plain,(
    ! [A_48,B_49,C_50] :
      ( r2_hidden('#skF_5'(A_48,B_49,C_50),B_49)
      | ~ r2_hidden(A_48,k10_relat_1(C_50,B_49))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_539,plain,(
    ! [A_175,B_176,C_177] :
      ( r2_hidden(k4_tarski(A_175,'#skF_5'(A_175,B_176,C_177)),C_177)
      | ~ r2_hidden(A_175,k10_relat_1(C_177,B_176))
      | ~ v1_relat_1(C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [C_56,A_54,B_55] :
      ( k1_funct_1(C_56,A_54) = B_55
      | ~ r2_hidden(k4_tarski(A_54,B_55),C_56)
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_703,plain,(
    ! [C_205,A_206,B_207] :
      ( k1_funct_1(C_205,A_206) = '#skF_5'(A_206,B_207,C_205)
      | ~ v1_funct_1(C_205)
      | ~ r2_hidden(A_206,k10_relat_1(C_205,B_207))
      | ~ v1_relat_1(C_205) ) ),
    inference(resolution,[status(thm)],[c_539,c_34])).

tff(c_730,plain,
    ( k1_funct_1('#skF_9','#skF_11') = '#skF_5'('#skF_11','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_514,c_703])).

tff(c_745,plain,(
    k1_funct_1('#skF_9','#skF_11') = '#skF_5'('#skF_11','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64,c_730])).

tff(c_70,plain,
    ( r2_hidden('#skF_10','#skF_6')
    | ~ r2_hidden(k1_funct_1('#skF_9','#skF_11'),'#skF_8')
    | ~ r2_hidden('#skF_11','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_86,plain,(
    ~ r2_hidden('#skF_11','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_87,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_91,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_87])).

tff(c_474,plain,(
    ! [B_145,A_146,C_147] :
      ( k1_xboole_0 = B_145
      | k1_relset_1(A_146,B_145,C_147) = A_146
      | ~ v1_funct_2(C_147,A_146,B_145)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_146,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_477,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_474])).

tff(c_480,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91,c_477])).

tff(c_481,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_480])).

tff(c_103,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k8_relset_1(A_91,B_92,C_93,D_94) = k10_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_106,plain,(
    ! [D_94] : k8_relset_1('#skF_6','#skF_7','#skF_9',D_94) = k10_relat_1('#skF_9',D_94) ),
    inference(resolution,[status(thm)],[c_60,c_103])).

tff(c_107,plain,(
    r2_hidden('#skF_11',k10_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_85])).

tff(c_147,plain,(
    ! [A_108,B_109,C_110] :
      ( r2_hidden(k4_tarski(A_108,'#skF_5'(A_108,B_109,C_110)),C_110)
      | ~ r2_hidden(A_108,k10_relat_1(C_110,B_109))
      | ~ v1_relat_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ! [A_54,C_56,B_55] :
      ( r2_hidden(A_54,k1_relat_1(C_56))
      | ~ r2_hidden(k4_tarski(A_54,B_55),C_56)
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_156,plain,(
    ! [A_111,C_112,B_113] :
      ( r2_hidden(A_111,k1_relat_1(C_112))
      | ~ v1_funct_1(C_112)
      | ~ r2_hidden(A_111,k10_relat_1(C_112,B_113))
      | ~ v1_relat_1(C_112) ) ),
    inference(resolution,[status(thm)],[c_147,c_36])).

tff(c_170,plain,
    ( r2_hidden('#skF_11',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_107,c_156])).

tff(c_181,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64,c_170])).

tff(c_485,plain,(
    r2_hidden('#skF_11','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_181])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_485])).

tff(c_490,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_9','#skF_11'),'#skF_8')
    | r2_hidden('#skF_10','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_492,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_11'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_747,plain,(
    ~ r2_hidden('#skF_5'('#skF_11','#skF_8','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_492])).

tff(c_759,plain,
    ( ~ r2_hidden('#skF_11',k10_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_747])).

tff(c_763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_514,c_759])).

tff(c_764,plain,(
    r2_hidden('#skF_10','#skF_6') ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_766,plain,(
    ! [A_208,B_209,C_210] :
      ( k1_relset_1(A_208,B_209,C_210) = k1_relat_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_770,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_766])).

tff(c_1103,plain,(
    ! [B_274,A_275,C_276] :
      ( k1_xboole_0 = B_274
      | k1_relset_1(A_275,B_274,C_276) = A_275
      | ~ v1_funct_2(C_276,A_275,B_274)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_275,B_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1106,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1103])).

tff(c_1109,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_770,c_1106])).

tff(c_1110,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1109])).

tff(c_491,plain,(
    r2_hidden('#skF_11','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_765,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_11'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_782,plain,(
    ! [A_221,B_222,C_223,D_224] :
      ( k8_relset_1(A_221,B_222,C_223,D_224) = k10_relat_1(C_223,D_224)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_785,plain,(
    ! [D_224] : k8_relset_1('#skF_6','#skF_7','#skF_9',D_224) = k10_relat_1('#skF_9',D_224) ),
    inference(resolution,[status(thm)],[c_60,c_782])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_7','#skF_9','#skF_8'))
    | ~ r2_hidden(k1_funct_1('#skF_9','#skF_11'),'#skF_8')
    | ~ r2_hidden('#skF_11','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_890,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_765,c_785,c_66])).

tff(c_935,plain,(
    ! [A_253,C_254] :
      ( r2_hidden(k4_tarski(A_253,k1_funct_1(C_254,A_253)),C_254)
      | ~ r2_hidden(A_253,k1_relat_1(C_254))
      | ~ v1_funct_1(C_254)
      | ~ v1_relat_1(C_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_10'),'#skF_8')
    | ~ r2_hidden(k1_funct_1('#skF_9','#skF_11'),'#skF_8')
    | ~ r2_hidden('#skF_11','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_780,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_765,c_68])).

tff(c_799,plain,(
    ! [D_231,A_232,B_233,E_234] :
      ( r2_hidden(D_231,k10_relat_1(A_232,B_233))
      | ~ r2_hidden(E_234,B_233)
      | ~ r2_hidden(k4_tarski(D_231,E_234),A_232)
      | ~ v1_relat_1(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_816,plain,(
    ! [D_231,A_232] :
      ( r2_hidden(D_231,k10_relat_1(A_232,'#skF_8'))
      | ~ r2_hidden(k4_tarski(D_231,k1_funct_1('#skF_9','#skF_10')),A_232)
      | ~ v1_relat_1(A_232) ) ),
    inference(resolution,[status(thm)],[c_780,c_799])).

tff(c_947,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_8'))
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_935,c_816])).

tff(c_962,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_8'))
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64,c_947])).

tff(c_963,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_890,c_962])).

tff(c_1114,plain,(
    ~ r2_hidden('#skF_10','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_963])).

tff(c_1120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_1114])).

tff(c_1121,plain,(
    r2_hidden('#skF_10','#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1124,plain,(
    ! [A_277,B_278,C_279] :
      ( k1_relset_1(A_277,B_278,C_279) = k1_relat_1(C_279)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1128,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_1124])).

tff(c_1318,plain,(
    ! [B_337,A_338,C_339] :
      ( k1_xboole_0 = B_337
      | k1_relset_1(A_338,B_337,C_339) = A_338
      | ~ v1_funct_2(C_339,A_338,B_337)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1321,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1318])).

tff(c_1324,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1128,c_1321])).

tff(c_1325,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1324])).

tff(c_1139,plain,(
    ! [A_290,B_291,C_292,D_293] :
      ( k8_relset_1(A_290,B_291,C_292,D_293) = k10_relat_1(C_292,D_293)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1142,plain,(
    ! [D_293] : k8_relset_1('#skF_6','#skF_7','#skF_9',D_293) = k10_relat_1('#skF_9',D_293) ),
    inference(resolution,[status(thm)],[c_60,c_1139])).

tff(c_1122,plain,(
    ~ r2_hidden('#skF_11',k8_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_72,plain,
    ( ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_7','#skF_9','#skF_8'))
    | r2_hidden('#skF_11',k8_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1143,plain,(
    ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1122,c_72])).

tff(c_1144,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_1143])).

tff(c_32,plain,(
    ! [A_54,C_56] :
      ( r2_hidden(k4_tarski(A_54,k1_funct_1(C_56,A_54)),C_56)
      | ~ r2_hidden(A_54,k1_relat_1(C_56))
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_74,plain,
    ( r2_hidden(k1_funct_1('#skF_9','#skF_10'),'#skF_8')
    | r2_hidden('#skF_11',k8_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1133,plain,(
    r2_hidden(k1_funct_1('#skF_9','#skF_10'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1122,c_74])).

tff(c_1192,plain,(
    ! [D_308,A_309,B_310,E_311] :
      ( r2_hidden(D_308,k10_relat_1(A_309,B_310))
      | ~ r2_hidden(E_311,B_310)
      | ~ r2_hidden(k4_tarski(D_308,E_311),A_309)
      | ~ v1_relat_1(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1213,plain,(
    ! [D_314,A_315] :
      ( r2_hidden(D_314,k10_relat_1(A_315,'#skF_8'))
      | ~ r2_hidden(k4_tarski(D_314,k1_funct_1('#skF_9','#skF_10')),A_315)
      | ~ v1_relat_1(A_315) ) ),
    inference(resolution,[status(thm)],[c_1133,c_1192])).

tff(c_1217,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_8'))
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_9'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_1213])).

tff(c_1220,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_8'))
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64,c_1217])).

tff(c_1221,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_1144,c_1220])).

tff(c_1330,plain,(
    ~ r2_hidden('#skF_10','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_1221])).

tff(c_1334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.67  
% 3.52/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.68  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.52/1.68  
% 3.52/1.68  %Foreground sorts:
% 3.52/1.68  
% 3.52/1.68  
% 3.52/1.68  %Background operators:
% 3.52/1.68  
% 3.52/1.68  
% 3.52/1.68  %Foreground operators:
% 3.52/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.52/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.52/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.52/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.68  tff('#skF_11', type, '#skF_11': $i).
% 3.52/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.52/1.68  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.52/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.52/1.68  tff('#skF_10', type, '#skF_10': $i).
% 3.52/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.52/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.52/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.52/1.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.52/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.52/1.68  tff('#skF_9', type, '#skF_9': $i).
% 3.52/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.52/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.52/1.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.52/1.68  tff('#skF_8', type, '#skF_8': $i).
% 3.52/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.52/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.52/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.68  
% 3.80/1.69  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.80/1.69  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: (r2_hidden(E, k8_relset_1(A, B, D, C)) <=> (r2_hidden(E, A) & r2_hidden(k1_funct_1(D, E), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_funct_2)).
% 3.80/1.69  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.80/1.69  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.80/1.69  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.80/1.69  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.80/1.69  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.80/1.69  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.80/1.69  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 3.80/1.69  tff(c_22, plain, (![A_46, B_47]: (v1_relat_1(k2_zfmisc_1(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.80/1.69  tff(c_60, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.69  tff(c_78, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.69  tff(c_81, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_78])).
% 3.80/1.69  tff(c_84, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_81])).
% 3.80/1.69  tff(c_509, plain, (![A_161, B_162, C_163, D_164]: (k8_relset_1(A_161, B_162, C_163, D_164)=k10_relat_1(C_163, D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.80/1.69  tff(c_512, plain, (![D_164]: (k8_relset_1('#skF_6', '#skF_7', '#skF_9', D_164)=k10_relat_1('#skF_9', D_164))), inference(resolution, [status(thm)], [c_60, c_509])).
% 3.80/1.69  tff(c_76, plain, (r2_hidden('#skF_10', '#skF_6') | r2_hidden('#skF_11', k8_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.69  tff(c_85, plain, (r2_hidden('#skF_11', k8_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(splitLeft, [status(thm)], [c_76])).
% 3.80/1.69  tff(c_514, plain, (r2_hidden('#skF_11', k10_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_85])).
% 3.80/1.69  tff(c_26, plain, (![A_48, B_49, C_50]: (r2_hidden('#skF_5'(A_48, B_49, C_50), B_49) | ~r2_hidden(A_48, k10_relat_1(C_50, B_49)) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.69  tff(c_64, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.69  tff(c_539, plain, (![A_175, B_176, C_177]: (r2_hidden(k4_tarski(A_175, '#skF_5'(A_175, B_176, C_177)), C_177) | ~r2_hidden(A_175, k10_relat_1(C_177, B_176)) | ~v1_relat_1(C_177))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.69  tff(c_34, plain, (![C_56, A_54, B_55]: (k1_funct_1(C_56, A_54)=B_55 | ~r2_hidden(k4_tarski(A_54, B_55), C_56) | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.80/1.69  tff(c_703, plain, (![C_205, A_206, B_207]: (k1_funct_1(C_205, A_206)='#skF_5'(A_206, B_207, C_205) | ~v1_funct_1(C_205) | ~r2_hidden(A_206, k10_relat_1(C_205, B_207)) | ~v1_relat_1(C_205))), inference(resolution, [status(thm)], [c_539, c_34])).
% 3.80/1.69  tff(c_730, plain, (k1_funct_1('#skF_9', '#skF_11')='#skF_5'('#skF_11', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_514, c_703])).
% 3.80/1.69  tff(c_745, plain, (k1_funct_1('#skF_9', '#skF_11')='#skF_5'('#skF_11', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64, c_730])).
% 3.80/1.69  tff(c_70, plain, (r2_hidden('#skF_10', '#skF_6') | ~r2_hidden(k1_funct_1('#skF_9', '#skF_11'), '#skF_8') | ~r2_hidden('#skF_11', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.69  tff(c_86, plain, (~r2_hidden('#skF_11', '#skF_6')), inference(splitLeft, [status(thm)], [c_70])).
% 3.80/1.69  tff(c_58, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.69  tff(c_62, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.69  tff(c_87, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.80/1.69  tff(c_91, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_87])).
% 3.80/1.69  tff(c_474, plain, (![B_145, A_146, C_147]: (k1_xboole_0=B_145 | k1_relset_1(A_146, B_145, C_147)=A_146 | ~v1_funct_2(C_147, A_146, B_145) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_146, B_145))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.80/1.69  tff(c_477, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_474])).
% 3.80/1.69  tff(c_480, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91, c_477])).
% 3.80/1.69  tff(c_481, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_480])).
% 3.80/1.69  tff(c_103, plain, (![A_91, B_92, C_93, D_94]: (k8_relset_1(A_91, B_92, C_93, D_94)=k10_relat_1(C_93, D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.80/1.69  tff(c_106, plain, (![D_94]: (k8_relset_1('#skF_6', '#skF_7', '#skF_9', D_94)=k10_relat_1('#skF_9', D_94))), inference(resolution, [status(thm)], [c_60, c_103])).
% 3.80/1.69  tff(c_107, plain, (r2_hidden('#skF_11', k10_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_85])).
% 3.80/1.69  tff(c_147, plain, (![A_108, B_109, C_110]: (r2_hidden(k4_tarski(A_108, '#skF_5'(A_108, B_109, C_110)), C_110) | ~r2_hidden(A_108, k10_relat_1(C_110, B_109)) | ~v1_relat_1(C_110))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.69  tff(c_36, plain, (![A_54, C_56, B_55]: (r2_hidden(A_54, k1_relat_1(C_56)) | ~r2_hidden(k4_tarski(A_54, B_55), C_56) | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.80/1.69  tff(c_156, plain, (![A_111, C_112, B_113]: (r2_hidden(A_111, k1_relat_1(C_112)) | ~v1_funct_1(C_112) | ~r2_hidden(A_111, k10_relat_1(C_112, B_113)) | ~v1_relat_1(C_112))), inference(resolution, [status(thm)], [c_147, c_36])).
% 3.80/1.69  tff(c_170, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_107, c_156])).
% 3.80/1.69  tff(c_181, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64, c_170])).
% 3.80/1.69  tff(c_485, plain, (r2_hidden('#skF_11', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_481, c_181])).
% 3.80/1.69  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_485])).
% 3.80/1.69  tff(c_490, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_11'), '#skF_8') | r2_hidden('#skF_10', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 3.80/1.69  tff(c_492, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_11'), '#skF_8')), inference(splitLeft, [status(thm)], [c_490])).
% 3.80/1.69  tff(c_747, plain, (~r2_hidden('#skF_5'('#skF_11', '#skF_8', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_745, c_492])).
% 3.80/1.69  tff(c_759, plain, (~r2_hidden('#skF_11', k10_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_747])).
% 3.80/1.69  tff(c_763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_514, c_759])).
% 3.80/1.69  tff(c_764, plain, (r2_hidden('#skF_10', '#skF_6')), inference(splitRight, [status(thm)], [c_490])).
% 3.80/1.69  tff(c_766, plain, (![A_208, B_209, C_210]: (k1_relset_1(A_208, B_209, C_210)=k1_relat_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.80/1.69  tff(c_770, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_766])).
% 3.80/1.69  tff(c_1103, plain, (![B_274, A_275, C_276]: (k1_xboole_0=B_274 | k1_relset_1(A_275, B_274, C_276)=A_275 | ~v1_funct_2(C_276, A_275, B_274) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_275, B_274))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.80/1.69  tff(c_1106, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_1103])).
% 3.80/1.69  tff(c_1109, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_770, c_1106])).
% 3.80/1.69  tff(c_1110, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_1109])).
% 3.80/1.69  tff(c_491, plain, (r2_hidden('#skF_11', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 3.80/1.69  tff(c_765, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_11'), '#skF_8')), inference(splitRight, [status(thm)], [c_490])).
% 3.80/1.69  tff(c_782, plain, (![A_221, B_222, C_223, D_224]: (k8_relset_1(A_221, B_222, C_223, D_224)=k10_relat_1(C_223, D_224) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.80/1.69  tff(c_785, plain, (![D_224]: (k8_relset_1('#skF_6', '#skF_7', '#skF_9', D_224)=k10_relat_1('#skF_9', D_224))), inference(resolution, [status(thm)], [c_60, c_782])).
% 3.80/1.69  tff(c_66, plain, (~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8')) | ~r2_hidden(k1_funct_1('#skF_9', '#skF_11'), '#skF_8') | ~r2_hidden('#skF_11', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.69  tff(c_890, plain, (~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_491, c_765, c_785, c_66])).
% 3.80/1.69  tff(c_935, plain, (![A_253, C_254]: (r2_hidden(k4_tarski(A_253, k1_funct_1(C_254, A_253)), C_254) | ~r2_hidden(A_253, k1_relat_1(C_254)) | ~v1_funct_1(C_254) | ~v1_relat_1(C_254))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.80/1.69  tff(c_68, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_10'), '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', '#skF_11'), '#skF_8') | ~r2_hidden('#skF_11', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.69  tff(c_780, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_491, c_765, c_68])).
% 3.80/1.69  tff(c_799, plain, (![D_231, A_232, B_233, E_234]: (r2_hidden(D_231, k10_relat_1(A_232, B_233)) | ~r2_hidden(E_234, B_233) | ~r2_hidden(k4_tarski(D_231, E_234), A_232) | ~v1_relat_1(A_232))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.80/1.69  tff(c_816, plain, (![D_231, A_232]: (r2_hidden(D_231, k10_relat_1(A_232, '#skF_8')) | ~r2_hidden(k4_tarski(D_231, k1_funct_1('#skF_9', '#skF_10')), A_232) | ~v1_relat_1(A_232))), inference(resolution, [status(thm)], [c_780, c_799])).
% 3.80/1.69  tff(c_947, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_8')) | ~r2_hidden('#skF_10', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_935, c_816])).
% 3.80/1.69  tff(c_962, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_8')) | ~r2_hidden('#skF_10', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64, c_947])).
% 3.80/1.69  tff(c_963, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_890, c_962])).
% 3.80/1.69  tff(c_1114, plain, (~r2_hidden('#skF_10', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_963])).
% 3.80/1.69  tff(c_1120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_764, c_1114])).
% 3.80/1.69  tff(c_1121, plain, (r2_hidden('#skF_10', '#skF_6')), inference(splitRight, [status(thm)], [c_76])).
% 3.80/1.69  tff(c_1124, plain, (![A_277, B_278, C_279]: (k1_relset_1(A_277, B_278, C_279)=k1_relat_1(C_279) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.80/1.69  tff(c_1128, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_1124])).
% 3.80/1.69  tff(c_1318, plain, (![B_337, A_338, C_339]: (k1_xboole_0=B_337 | k1_relset_1(A_338, B_337, C_339)=A_338 | ~v1_funct_2(C_339, A_338, B_337) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.80/1.69  tff(c_1321, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_1318])).
% 3.80/1.69  tff(c_1324, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1128, c_1321])).
% 3.80/1.69  tff(c_1325, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_1324])).
% 3.80/1.69  tff(c_1139, plain, (![A_290, B_291, C_292, D_293]: (k8_relset_1(A_290, B_291, C_292, D_293)=k10_relat_1(C_292, D_293) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.80/1.69  tff(c_1142, plain, (![D_293]: (k8_relset_1('#skF_6', '#skF_7', '#skF_9', D_293)=k10_relat_1('#skF_9', D_293))), inference(resolution, [status(thm)], [c_60, c_1139])).
% 3.80/1.69  tff(c_1122, plain, (~r2_hidden('#skF_11', k8_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(splitRight, [status(thm)], [c_76])).
% 3.80/1.69  tff(c_72, plain, (~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8')) | r2_hidden('#skF_11', k8_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.69  tff(c_1143, plain, (~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1122, c_72])).
% 3.80/1.69  tff(c_1144, plain, (~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_1143])).
% 3.80/1.69  tff(c_32, plain, (![A_54, C_56]: (r2_hidden(k4_tarski(A_54, k1_funct_1(C_56, A_54)), C_56) | ~r2_hidden(A_54, k1_relat_1(C_56)) | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.80/1.69  tff(c_74, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_10'), '#skF_8') | r2_hidden('#skF_11', k8_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.80/1.69  tff(c_1133, plain, (r2_hidden(k1_funct_1('#skF_9', '#skF_10'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1122, c_74])).
% 3.80/1.69  tff(c_1192, plain, (![D_308, A_309, B_310, E_311]: (r2_hidden(D_308, k10_relat_1(A_309, B_310)) | ~r2_hidden(E_311, B_310) | ~r2_hidden(k4_tarski(D_308, E_311), A_309) | ~v1_relat_1(A_309))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.80/1.69  tff(c_1213, plain, (![D_314, A_315]: (r2_hidden(D_314, k10_relat_1(A_315, '#skF_8')) | ~r2_hidden(k4_tarski(D_314, k1_funct_1('#skF_9', '#skF_10')), A_315) | ~v1_relat_1(A_315))), inference(resolution, [status(thm)], [c_1133, c_1192])).
% 3.80/1.69  tff(c_1217, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_8')) | ~r2_hidden('#skF_10', k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_1213])).
% 3.80/1.69  tff(c_1220, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_8')) | ~r2_hidden('#skF_10', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64, c_1217])).
% 3.80/1.69  tff(c_1221, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1144, c_1220])).
% 3.80/1.69  tff(c_1330, plain, (~r2_hidden('#skF_10', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1325, c_1221])).
% 3.80/1.69  tff(c_1334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1330])).
% 3.80/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.69  
% 3.80/1.69  Inference rules
% 3.80/1.69  ----------------------
% 3.80/1.69  #Ref     : 0
% 3.80/1.69  #Sup     : 262
% 3.80/1.69  #Fact    : 0
% 3.80/1.69  #Define  : 0
% 3.80/1.69  #Split   : 3
% 3.80/1.69  #Chain   : 0
% 3.80/1.69  #Close   : 0
% 3.80/1.69  
% 3.80/1.69  Ordering : KBO
% 3.80/1.69  
% 3.80/1.69  Simplification rules
% 3.80/1.69  ----------------------
% 3.80/1.69  #Subsume      : 12
% 3.80/1.69  #Demod        : 161
% 3.80/1.69  #Tautology    : 70
% 3.80/1.69  #SimpNegUnit  : 10
% 3.80/1.69  #BackRed      : 26
% 3.80/1.69  
% 3.80/1.69  #Partial instantiations: 0
% 3.80/1.69  #Strategies tried      : 1
% 3.80/1.70  
% 3.80/1.70  Timing (in seconds)
% 3.80/1.70  ----------------------
% 3.80/1.70  Preprocessing        : 0.37
% 3.80/1.70  Parsing              : 0.19
% 3.80/1.70  CNF conversion       : 0.03
% 3.80/1.70  Main loop            : 0.48
% 3.80/1.70  Inferencing          : 0.18
% 3.80/1.70  Reduction            : 0.14
% 3.80/1.70  Demodulation         : 0.10
% 3.80/1.70  BG Simplification    : 0.03
% 3.80/1.70  Subsumption          : 0.08
% 3.80/1.70  Abstraction          : 0.03
% 3.80/1.70  MUC search           : 0.00
% 3.80/1.70  Cooper               : 0.00
% 3.80/1.70  Total                : 0.89
% 3.80/1.70  Index Insertion      : 0.00
% 3.80/1.70  Index Deletion       : 0.00
% 3.80/1.70  Index Matching       : 0.00
% 3.80/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
