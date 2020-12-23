%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:54 EST 2020

% Result     : Theorem 25.47s
% Output     : CNFRefutation 25.68s
% Verified   : 
% Statistics : Number of formulae       :  165 (4266 expanded)
%              Number of leaves         :   36 (1553 expanded)
%              Depth                    :   25
%              Number of atoms          :  505 (25746 expanded)
%              Number of equality atoms :  209 (10791 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & v2_funct_1(C)
                & ! [E,F] :
                    ( ( ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F )
                     => ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E ) )
                    & ( ( r2_hidden(F,A)
                        & k1_funct_1(C,F) = E )
                     => ( r2_hidden(E,B)
                        & k1_funct_1(D,E) = F ) ) ) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_2)).

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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k1_relat_1(A) = k2_relat_1(B)
              & k2_relat_1(A) = k1_relat_1(B)
              & ! [C,D] :
                  ( ( r2_hidden(C,k1_relat_1(A))
                    & r2_hidden(D,k1_relat_1(B)) )
                 => ( k1_funct_1(A,C) = D
                  <=> k1_funct_1(B,D) = C ) ) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_1)).

tff(c_52,plain,(
    k2_funct_1('#skF_9') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_87,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_68,c_87])).

tff(c_99,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_93])).

tff(c_72,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_58,plain,(
    v2_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_70,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_151,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_159,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_151])).

tff(c_308,plain,(
    ! [B_112,A_113,C_114] :
      ( k1_xboole_0 = B_112
      | k1_relset_1(A_113,B_112,C_114) = A_113
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_314,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_308])).

tff(c_321,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_159,c_314])).

tff(c_322,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_321])).

tff(c_60,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_133,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_139,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_133])).

tff(c_142,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_139])).

tff(c_62,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_90,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_87])).

tff(c_96,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_90])).

tff(c_66,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_64,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_158,plain,(
    k1_relset_1('#skF_8','#skF_7','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_151])).

tff(c_311,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_8','#skF_7','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_308])).

tff(c_317,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_158,c_311])).

tff(c_318,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_317])).

tff(c_347,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_2'(A_115,B_116),k1_relat_1(A_115))
      | r2_hidden('#skF_3'(A_115,B_116),B_116)
      | k2_relat_1(A_115) = B_116
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_353,plain,(
    ! [B_116] :
      ( r2_hidden('#skF_2'('#skF_10',B_116),'#skF_8')
      | r2_hidden('#skF_3'('#skF_10',B_116),B_116)
      | k2_relat_1('#skF_10') = B_116
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_347])).

tff(c_357,plain,(
    ! [B_116] :
      ( r2_hidden('#skF_2'('#skF_10',B_116),'#skF_8')
      | r2_hidden('#skF_3'('#skF_10',B_116),B_116)
      | k2_relat_1('#skF_10') = B_116 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_353])).

tff(c_80,plain,(
    ! [F_72] :
      ( r2_hidden(k1_funct_1('#skF_9',F_72),'#skF_8')
      | ~ r2_hidden(F_72,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_78,plain,(
    ! [F_72] :
      ( k1_funct_1('#skF_10',k1_funct_1('#skF_9',F_72)) = F_72
      | ~ r2_hidden(F_72,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_59206,plain,(
    ! [A_1013,B_1014,D_1015] :
      ( r2_hidden('#skF_2'(A_1013,B_1014),k1_relat_1(A_1013))
      | k1_funct_1(A_1013,D_1015) != '#skF_3'(A_1013,B_1014)
      | ~ r2_hidden(D_1015,k1_relat_1(A_1013))
      | k2_relat_1(A_1013) = B_1014
      | ~ v1_funct_1(A_1013)
      | ~ v1_relat_1(A_1013) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59216,plain,(
    ! [B_1014,F_72] :
      ( r2_hidden('#skF_2'('#skF_10',B_1014),k1_relat_1('#skF_10'))
      | F_72 != '#skF_3'('#skF_10',B_1014)
      | ~ r2_hidden(k1_funct_1('#skF_9',F_72),k1_relat_1('#skF_10'))
      | k2_relat_1('#skF_10') = B_1014
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(F_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_59206])).

tff(c_59224,plain,(
    ! [B_1014,F_72] :
      ( r2_hidden('#skF_2'('#skF_10',B_1014),'#skF_8')
      | F_72 != '#skF_3'('#skF_10',B_1014)
      | ~ r2_hidden(k1_funct_1('#skF_9',F_72),'#skF_8')
      | k2_relat_1('#skF_10') = B_1014
      | ~ r2_hidden(F_72,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_318,c_318,c_59216])).

tff(c_60169,plain,(
    ! [B_1052] :
      ( r2_hidden('#skF_2'('#skF_10',B_1052),'#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_9','#skF_3'('#skF_10',B_1052)),'#skF_8')
      | k2_relat_1('#skF_10') = B_1052
      | ~ r2_hidden('#skF_3'('#skF_10',B_1052),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_59224])).

tff(c_60388,plain,(
    ! [B_1055] :
      ( r2_hidden('#skF_2'('#skF_10',B_1055),'#skF_8')
      | k2_relat_1('#skF_10') = B_1055
      | ~ r2_hidden('#skF_3'('#skF_10',B_1055),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_80,c_60169])).

tff(c_60403,plain,
    ( r2_hidden('#skF_2'('#skF_10','#skF_7'),'#skF_8')
    | k2_relat_1('#skF_10') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_357,c_60388])).

tff(c_60410,plain,(
    k2_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_60403])).

tff(c_59617,plain,(
    ! [A_1028,B_1029] :
      ( r2_hidden('#skF_6'(A_1028,B_1029),k1_relat_1(B_1029))
      | k2_funct_1(A_1028) = B_1029
      | k2_relat_1(A_1028) != k1_relat_1(B_1029)
      | k2_relat_1(B_1029) != k1_relat_1(A_1028)
      | ~ v2_funct_1(A_1028)
      | ~ v1_funct_1(B_1029)
      | ~ v1_relat_1(B_1029)
      | ~ v1_funct_1(A_1028)
      | ~ v1_relat_1(A_1028) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_59623,plain,(
    ! [A_1028] :
      ( r2_hidden('#skF_6'(A_1028,'#skF_10'),'#skF_8')
      | k2_funct_1(A_1028) = '#skF_10'
      | k2_relat_1(A_1028) != k1_relat_1('#skF_10')
      | k2_relat_1('#skF_10') != k1_relat_1(A_1028)
      | ~ v2_funct_1(A_1028)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ v1_funct_1(A_1028)
      | ~ v1_relat_1(A_1028) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_59617])).

tff(c_59627,plain,(
    ! [A_1028] :
      ( r2_hidden('#skF_6'(A_1028,'#skF_10'),'#skF_8')
      | k2_funct_1(A_1028) = '#skF_10'
      | k2_relat_1(A_1028) != '#skF_8'
      | k2_relat_1('#skF_10') != k1_relat_1(A_1028)
      | ~ v2_funct_1(A_1028)
      | ~ v1_funct_1(A_1028)
      | ~ v1_relat_1(A_1028) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_318,c_59623])).

tff(c_65249,plain,(
    ! [A_1184] :
      ( r2_hidden('#skF_6'(A_1184,'#skF_10'),'#skF_8')
      | k2_funct_1(A_1184) = '#skF_10'
      | k2_relat_1(A_1184) != '#skF_8'
      | k1_relat_1(A_1184) != '#skF_7'
      | ~ v2_funct_1(A_1184)
      | ~ v1_funct_1(A_1184)
      | ~ v1_relat_1(A_1184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60410,c_59627])).

tff(c_59770,plain,(
    ! [A_1036,B_1037] :
      ( r2_hidden('#skF_5'(A_1036,B_1037),k1_relat_1(A_1036))
      | k2_funct_1(A_1036) = B_1037
      | k2_relat_1(A_1036) != k1_relat_1(B_1037)
      | k2_relat_1(B_1037) != k1_relat_1(A_1036)
      | ~ v2_funct_1(A_1036)
      | ~ v1_funct_1(B_1037)
      | ~ v1_relat_1(B_1037)
      | ~ v1_funct_1(A_1036)
      | ~ v1_relat_1(A_1036) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_59773,plain,(
    ! [B_1037] :
      ( r2_hidden('#skF_5'('#skF_9',B_1037),'#skF_7')
      | k2_funct_1('#skF_9') = B_1037
      | k2_relat_1('#skF_9') != k1_relat_1(B_1037)
      | k2_relat_1(B_1037) != k1_relat_1('#skF_9')
      | ~ v2_funct_1('#skF_9')
      | ~ v1_funct_1(B_1037)
      | ~ v1_relat_1(B_1037)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_59770])).

tff(c_59778,plain,(
    ! [B_1037] :
      ( r2_hidden('#skF_5'('#skF_9',B_1037),'#skF_7')
      | k2_funct_1('#skF_9') = B_1037
      | k1_relat_1(B_1037) != '#skF_8'
      | k2_relat_1(B_1037) != '#skF_7'
      | ~ v1_funct_1(B_1037)
      | ~ v1_relat_1(B_1037) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_72,c_58,c_322,c_142,c_59773])).

tff(c_60174,plain,(
    ! [A_1053,B_1054] :
      ( k1_funct_1(A_1053,'#skF_5'(A_1053,B_1054)) = '#skF_6'(A_1053,B_1054)
      | k1_funct_1(B_1054,'#skF_6'(A_1053,B_1054)) = '#skF_5'(A_1053,B_1054)
      | k2_funct_1(A_1053) = B_1054
      | k2_relat_1(A_1053) != k1_relat_1(B_1054)
      | k2_relat_1(B_1054) != k1_relat_1(A_1053)
      | ~ v2_funct_1(A_1053)
      | ~ v1_funct_1(B_1054)
      | ~ v1_relat_1(B_1054)
      | ~ v1_funct_1(A_1053)
      | ~ v1_relat_1(A_1053) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_60244,plain,(
    ! [B_1054] :
      ( r2_hidden('#skF_6'('#skF_9',B_1054),'#skF_8')
      | ~ r2_hidden('#skF_5'('#skF_9',B_1054),'#skF_7')
      | k1_funct_1(B_1054,'#skF_6'('#skF_9',B_1054)) = '#skF_5'('#skF_9',B_1054)
      | k2_funct_1('#skF_9') = B_1054
      | k2_relat_1('#skF_9') != k1_relat_1(B_1054)
      | k2_relat_1(B_1054) != k1_relat_1('#skF_9')
      | ~ v2_funct_1('#skF_9')
      | ~ v1_funct_1(B_1054)
      | ~ v1_relat_1(B_1054)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60174,c_80])).

tff(c_60353,plain,(
    ! [B_1054] :
      ( r2_hidden('#skF_6'('#skF_9',B_1054),'#skF_8')
      | ~ r2_hidden('#skF_5'('#skF_9',B_1054),'#skF_7')
      | k1_funct_1(B_1054,'#skF_6'('#skF_9',B_1054)) = '#skF_5'('#skF_9',B_1054)
      | k2_funct_1('#skF_9') = B_1054
      | k1_relat_1(B_1054) != '#skF_8'
      | k2_relat_1(B_1054) != '#skF_7'
      | ~ v1_funct_1(B_1054)
      | ~ v1_relat_1(B_1054) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_72,c_58,c_322,c_142,c_60244])).

tff(c_74,plain,(
    ! [E_71] :
      ( k1_funct_1('#skF_9',k1_funct_1('#skF_10',E_71)) = E_71
      | ~ r2_hidden(E_71,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_60308,plain,(
    ! [A_1053] :
      ( k1_funct_1('#skF_9','#skF_5'(A_1053,'#skF_10')) = '#skF_6'(A_1053,'#skF_10')
      | ~ r2_hidden('#skF_6'(A_1053,'#skF_10'),'#skF_8')
      | k1_funct_1(A_1053,'#skF_5'(A_1053,'#skF_10')) = '#skF_6'(A_1053,'#skF_10')
      | k2_funct_1(A_1053) = '#skF_10'
      | k2_relat_1(A_1053) != k1_relat_1('#skF_10')
      | k2_relat_1('#skF_10') != k1_relat_1(A_1053)
      | ~ v2_funct_1(A_1053)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ v1_funct_1(A_1053)
      | ~ v1_relat_1(A_1053) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60174,c_74])).

tff(c_60381,plain,(
    ! [A_1053] :
      ( k1_funct_1('#skF_9','#skF_5'(A_1053,'#skF_10')) = '#skF_6'(A_1053,'#skF_10')
      | ~ r2_hidden('#skF_6'(A_1053,'#skF_10'),'#skF_8')
      | k1_funct_1(A_1053,'#skF_5'(A_1053,'#skF_10')) = '#skF_6'(A_1053,'#skF_10')
      | k2_funct_1(A_1053) = '#skF_10'
      | k2_relat_1(A_1053) != '#skF_8'
      | k2_relat_1('#skF_10') != k1_relat_1(A_1053)
      | ~ v2_funct_1(A_1053)
      | ~ v1_funct_1(A_1053)
      | ~ v1_relat_1(A_1053) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_318,c_60308])).

tff(c_62465,plain,(
    ! [A_1116] :
      ( k1_funct_1('#skF_9','#skF_5'(A_1116,'#skF_10')) = '#skF_6'(A_1116,'#skF_10')
      | ~ r2_hidden('#skF_6'(A_1116,'#skF_10'),'#skF_8')
      | k1_funct_1(A_1116,'#skF_5'(A_1116,'#skF_10')) = '#skF_6'(A_1116,'#skF_10')
      | k2_funct_1(A_1116) = '#skF_10'
      | k2_relat_1(A_1116) != '#skF_8'
      | k1_relat_1(A_1116) != '#skF_7'
      | ~ v2_funct_1(A_1116)
      | ~ v1_funct_1(A_1116)
      | ~ v1_relat_1(A_1116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60410,c_60381])).

tff(c_62468,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_10')) = '#skF_6'('#skF_9','#skF_10')
    | k2_relat_1('#skF_9') != '#skF_8'
    | k1_relat_1('#skF_9') != '#skF_7'
    | ~ v2_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_5'('#skF_9','#skF_10'),'#skF_7')
    | k1_funct_1('#skF_10','#skF_6'('#skF_9','#skF_10')) = '#skF_5'('#skF_9','#skF_10')
    | k2_funct_1('#skF_9') = '#skF_10'
    | k1_relat_1('#skF_10') != '#skF_8'
    | k2_relat_1('#skF_10') != '#skF_7'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_60353,c_62465])).

tff(c_62471,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_10')) = '#skF_6'('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_5'('#skF_9','#skF_10'),'#skF_7')
    | k1_funct_1('#skF_10','#skF_6'('#skF_9','#skF_10')) = '#skF_5'('#skF_9','#skF_10')
    | k2_funct_1('#skF_9') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_60410,c_318,c_99,c_72,c_58,c_322,c_142,c_62468])).

tff(c_62472,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_10')) = '#skF_6'('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_5'('#skF_9','#skF_10'),'#skF_7')
    | k1_funct_1('#skF_10','#skF_6'('#skF_9','#skF_10')) = '#skF_5'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_62471])).

tff(c_62673,plain,(
    ~ r2_hidden('#skF_5'('#skF_9','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_62472])).

tff(c_62676,plain,
    ( k2_funct_1('#skF_9') = '#skF_10'
    | k1_relat_1('#skF_10') != '#skF_8'
    | k2_relat_1('#skF_10') != '#skF_7'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_59778,c_62673])).

tff(c_62679,plain,(
    k2_funct_1('#skF_9') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_60410,c_318,c_62676])).

tff(c_62681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_62679])).

tff(c_62683,plain,(
    r2_hidden('#skF_5'('#skF_9','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_62472])).

tff(c_10,plain,(
    ! [A_6,C_42] :
      ( r2_hidden('#skF_4'(A_6,k2_relat_1(A_6),C_42),k1_relat_1(A_6))
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_329,plain,(
    ! [C_42] :
      ( r2_hidden('#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_42),'#skF_8')
      | ~ r2_hidden(C_42,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_10])).

tff(c_333,plain,(
    ! [C_42] :
      ( r2_hidden('#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_42),'#skF_8')
      | ~ r2_hidden(C_42,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_329])).

tff(c_207,plain,(
    ! [A_102,C_103] :
      ( k1_funct_1(A_102,'#skF_4'(A_102,k2_relat_1(A_102),C_103)) = C_103
      | ~ r2_hidden(C_103,k2_relat_1(A_102))
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_233,plain,(
    ! [C_103] :
      ( '#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_103) = k1_funct_1('#skF_9',C_103)
      | ~ r2_hidden('#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_103),'#skF_8')
      | ~ r2_hidden(C_103,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_74])).

tff(c_59135,plain,(
    ! [C_1010] :
      ( '#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_1010) = k1_funct_1('#skF_9',C_1010)
      | ~ r2_hidden('#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_1010),'#skF_8')
      | ~ r2_hidden(C_1010,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_233])).

tff(c_59139,plain,(
    ! [C_42] :
      ( '#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_42) = k1_funct_1('#skF_9',C_42)
      | ~ r2_hidden(C_42,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_333,c_59135])).

tff(c_60428,plain,(
    ! [C_42] :
      ( k1_funct_1('#skF_9',C_42) = '#skF_4'('#skF_10','#skF_7',C_42)
      | ~ r2_hidden(C_42,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60410,c_60410,c_59139])).

tff(c_62693,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_10')) = '#skF_4'('#skF_10','#skF_7','#skF_5'('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_62683,c_60428])).

tff(c_60232,plain,(
    ! [B_1054] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_9',B_1054)) = '#skF_5'('#skF_9',B_1054)
      | ~ r2_hidden('#skF_5'('#skF_9',B_1054),'#skF_7')
      | k1_funct_1(B_1054,'#skF_6'('#skF_9',B_1054)) = '#skF_5'('#skF_9',B_1054)
      | k2_funct_1('#skF_9') = B_1054
      | k2_relat_1('#skF_9') != k1_relat_1(B_1054)
      | k2_relat_1(B_1054) != k1_relat_1('#skF_9')
      | ~ v2_funct_1('#skF_9')
      | ~ v1_funct_1(B_1054)
      | ~ v1_relat_1(B_1054)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60174,c_78])).

tff(c_60347,plain,(
    ! [B_1054] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_9',B_1054)) = '#skF_5'('#skF_9',B_1054)
      | ~ r2_hidden('#skF_5'('#skF_9',B_1054),'#skF_7')
      | k1_funct_1(B_1054,'#skF_6'('#skF_9',B_1054)) = '#skF_5'('#skF_9',B_1054)
      | k2_funct_1('#skF_9') = B_1054
      | k1_relat_1(B_1054) != '#skF_8'
      | k2_relat_1(B_1054) != '#skF_7'
      | ~ v1_funct_1(B_1054)
      | ~ v1_relat_1(B_1054) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_72,c_58,c_322,c_142,c_60232])).

tff(c_62685,plain,
    ( k1_funct_1('#skF_10','#skF_6'('#skF_9','#skF_10')) = '#skF_5'('#skF_9','#skF_10')
    | k2_funct_1('#skF_9') = '#skF_10'
    | k1_relat_1('#skF_10') != '#skF_8'
    | k2_relat_1('#skF_10') != '#skF_7'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_62683,c_60347])).

tff(c_62691,plain,
    ( k1_funct_1('#skF_10','#skF_6'('#skF_9','#skF_10')) = '#skF_5'('#skF_9','#skF_10')
    | k2_funct_1('#skF_9') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_60410,c_318,c_62685])).

tff(c_62692,plain,(
    k1_funct_1('#skF_10','#skF_6'('#skF_9','#skF_10')) = '#skF_5'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_62691])).

tff(c_28,plain,(
    ! [B_52,A_46] :
      ( k1_funct_1(B_52,'#skF_6'(A_46,B_52)) != '#skF_5'(A_46,B_52)
      | k1_funct_1(A_46,'#skF_5'(A_46,B_52)) != '#skF_6'(A_46,B_52)
      | k2_funct_1(A_46) = B_52
      | k2_relat_1(A_46) != k1_relat_1(B_52)
      | k2_relat_1(B_52) != k1_relat_1(A_46)
      | ~ v2_funct_1(A_46)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62709,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_10')) != '#skF_6'('#skF_9','#skF_10')
    | k2_funct_1('#skF_9') = '#skF_10'
    | k2_relat_1('#skF_9') != k1_relat_1('#skF_10')
    | k2_relat_1('#skF_10') != k1_relat_1('#skF_9')
    | ~ v2_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_62692,c_28])).

tff(c_62743,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_10')) != '#skF_6'('#skF_9','#skF_10')
    | k2_funct_1('#skF_9') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_72,c_96,c_66,c_58,c_322,c_60410,c_142,c_318,c_62709])).

tff(c_62744,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_10')) != '#skF_6'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_62743])).

tff(c_62761,plain,(
    '#skF_4'('#skF_10','#skF_7','#skF_5'('#skF_9','#skF_10')) != '#skF_6'('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62693,c_62744])).

tff(c_62725,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_10')) = '#skF_6'('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_6'('#skF_9','#skF_10'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_62692,c_74])).

tff(c_62817,plain,
    ( '#skF_4'('#skF_10','#skF_7','#skF_5'('#skF_9','#skF_10')) = '#skF_6'('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_6'('#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62693,c_62725])).

tff(c_62818,plain,(
    ~ r2_hidden('#skF_6'('#skF_9','#skF_10'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_62761,c_62817])).

tff(c_65252,plain,
    ( k2_funct_1('#skF_9') = '#skF_10'
    | k2_relat_1('#skF_9') != '#skF_8'
    | k1_relat_1('#skF_9') != '#skF_7'
    | ~ v2_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_65249,c_62818])).

tff(c_65262,plain,(
    k2_funct_1('#skF_9') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_72,c_58,c_322,c_142,c_65252])).

tff(c_65264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_65262])).

tff(c_65266,plain,(
    k2_relat_1('#skF_10') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_60403])).

tff(c_65265,plain,(
    r2_hidden('#skF_2'('#skF_10','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_60403])).

tff(c_341,plain,(
    ! [C_42] :
      ( r2_hidden('#skF_4'('#skF_9',k2_relat_1('#skF_9'),C_42),'#skF_7')
      | ~ r2_hidden(C_42,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_10])).

tff(c_366,plain,(
    ! [C_117] :
      ( r2_hidden('#skF_4'('#skF_9','#skF_8',C_117),'#skF_7')
      | ~ r2_hidden(C_117,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_72,c_142,c_142,c_341])).

tff(c_229,plain,(
    ! [C_103] :
      ( '#skF_4'('#skF_9',k2_relat_1('#skF_9'),C_103) = k1_funct_1('#skF_10',C_103)
      | ~ r2_hidden('#skF_4'('#skF_9',k2_relat_1('#skF_9'),C_103),'#skF_7')
      | ~ r2_hidden(C_103,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_78])).

tff(c_256,plain,(
    ! [C_103] :
      ( k1_funct_1('#skF_10',C_103) = '#skF_4'('#skF_9','#skF_8',C_103)
      | ~ r2_hidden('#skF_4'('#skF_9','#skF_8',C_103),'#skF_7')
      | ~ r2_hidden(C_103,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_72,c_142,c_142,c_142,c_229])).

tff(c_370,plain,(
    ! [C_117] :
      ( k1_funct_1('#skF_10',C_117) = '#skF_4'('#skF_9','#skF_8',C_117)
      | ~ r2_hidden(C_117,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_366,c_256])).

tff(c_65270,plain,(
    k1_funct_1('#skF_10','#skF_2'('#skF_10','#skF_7')) = '#skF_4'('#skF_9','#skF_8','#skF_2'('#skF_10','#skF_7')) ),
    inference(resolution,[status(thm)],[c_65265,c_370])).

tff(c_20,plain,(
    ! [A_6,B_28] :
      ( k1_funct_1(A_6,'#skF_2'(A_6,B_28)) = '#skF_1'(A_6,B_28)
      | r2_hidden('#skF_3'(A_6,B_28),B_28)
      | k2_relat_1(A_6) = B_28
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59401,plain,(
    ! [A_1023,B_1024,D_1025] :
      ( k1_funct_1(A_1023,'#skF_2'(A_1023,B_1024)) = '#skF_1'(A_1023,B_1024)
      | k1_funct_1(A_1023,D_1025) != '#skF_3'(A_1023,B_1024)
      | ~ r2_hidden(D_1025,k1_relat_1(A_1023))
      | k2_relat_1(A_1023) = B_1024
      | ~ v1_funct_1(A_1023)
      | ~ v1_relat_1(A_1023) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59413,plain,(
    ! [B_1024,F_72] :
      ( k1_funct_1('#skF_10','#skF_2'('#skF_10',B_1024)) = '#skF_1'('#skF_10',B_1024)
      | F_72 != '#skF_3'('#skF_10',B_1024)
      | ~ r2_hidden(k1_funct_1('#skF_9',F_72),k1_relat_1('#skF_10'))
      | k2_relat_1('#skF_10') = B_1024
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(F_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_59401])).

tff(c_59423,plain,(
    ! [B_1024,F_72] :
      ( k1_funct_1('#skF_10','#skF_2'('#skF_10',B_1024)) = '#skF_1'('#skF_10',B_1024)
      | F_72 != '#skF_3'('#skF_10',B_1024)
      | ~ r2_hidden(k1_funct_1('#skF_9',F_72),'#skF_8')
      | k2_relat_1('#skF_10') = B_1024
      | ~ r2_hidden(F_72,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_318,c_59413])).

tff(c_67966,plain,(
    ! [B_1268] :
      ( k1_funct_1('#skF_10','#skF_2'('#skF_10',B_1268)) = '#skF_1'('#skF_10',B_1268)
      | ~ r2_hidden(k1_funct_1('#skF_9','#skF_3'('#skF_10',B_1268)),'#skF_8')
      | k2_relat_1('#skF_10') = B_1268
      | ~ r2_hidden('#skF_3'('#skF_10',B_1268),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_59423])).

tff(c_67971,plain,(
    ! [B_1269] :
      ( k1_funct_1('#skF_10','#skF_2'('#skF_10',B_1269)) = '#skF_1'('#skF_10',B_1269)
      | k2_relat_1('#skF_10') = B_1269
      | ~ r2_hidden('#skF_3'('#skF_10',B_1269),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_80,c_67966])).

tff(c_67995,plain,
    ( k1_funct_1('#skF_10','#skF_2'('#skF_10','#skF_7')) = '#skF_1'('#skF_10','#skF_7')
    | k2_relat_1('#skF_10') = '#skF_7'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_20,c_67971])).

tff(c_68014,plain,
    ( '#skF_4'('#skF_9','#skF_8','#skF_2'('#skF_10','#skF_7')) = '#skF_1'('#skF_10','#skF_7')
    | k2_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_65270,c_67995])).

tff(c_68015,plain,(
    '#skF_4'('#skF_9','#skF_8','#skF_2'('#skF_10','#skF_7')) = '#skF_1'('#skF_10','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_65266,c_68014])).

tff(c_76,plain,(
    ! [E_71] :
      ( r2_hidden(k1_funct_1('#skF_10',E_71),'#skF_7')
      | ~ r2_hidden(E_71,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_65303,plain,
    ( r2_hidden('#skF_4'('#skF_9','#skF_8','#skF_2'('#skF_10','#skF_7')),'#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_10','#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_65270,c_76])).

tff(c_65328,plain,(
    r2_hidden('#skF_4'('#skF_9','#skF_8','#skF_2'('#skF_10','#skF_7')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65265,c_65303])).

tff(c_68029,plain,(
    r2_hidden('#skF_1'('#skF_10','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68015,c_65328])).

tff(c_18,plain,(
    ! [A_6,B_28] :
      ( ~ r2_hidden('#skF_1'(A_6,B_28),B_28)
      | r2_hidden('#skF_3'(A_6,B_28),B_28)
      | k2_relat_1(A_6) = B_28
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_169,plain,(
    ! [A_88,D_89] :
      ( r2_hidden(k1_funct_1(A_88,D_89),k2_relat_1(A_88))
      | ~ r2_hidden(D_89,k1_relat_1(A_88))
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_175,plain,(
    ! [F_72] :
      ( r2_hidden(F_72,k2_relat_1('#skF_10'))
      | ~ r2_hidden(k1_funct_1('#skF_9',F_72),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(F_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_169])).

tff(c_182,plain,(
    ! [F_72] :
      ( r2_hidden(F_72,k2_relat_1('#skF_10'))
      | ~ r2_hidden(k1_funct_1('#skF_9',F_72),k1_relat_1('#skF_10'))
      | ~ r2_hidden(F_72,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_175])).

tff(c_424,plain,(
    ! [F_122] :
      ( r2_hidden(F_122,k2_relat_1('#skF_10'))
      | ~ r2_hidden(k1_funct_1('#skF_9',F_122),'#skF_8')
      | ~ r2_hidden(F_122,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_182])).

tff(c_440,plain,(
    ! [F_72] :
      ( r2_hidden(F_72,k2_relat_1('#skF_10'))
      | ~ r2_hidden(F_72,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_80,c_424])).

tff(c_8,plain,(
    ! [A_6,C_42] :
      ( k1_funct_1(A_6,'#skF_4'(A_6,k2_relat_1(A_6),C_42)) = C_42
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_6,B_28,D_41] :
      ( ~ r2_hidden('#skF_1'(A_6,B_28),B_28)
      | k1_funct_1(A_6,D_41) != '#skF_3'(A_6,B_28)
      | ~ r2_hidden(D_41,k1_relat_1(A_6))
      | k2_relat_1(A_6) = B_28
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68061,plain,(
    ! [D_41] :
      ( k1_funct_1('#skF_10',D_41) != '#skF_3'('#skF_10','#skF_7')
      | ~ r2_hidden(D_41,k1_relat_1('#skF_10'))
      | k2_relat_1('#skF_10') = '#skF_7'
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_68029,c_12])).

tff(c_68064,plain,(
    ! [D_41] :
      ( k1_funct_1('#skF_10',D_41) != '#skF_3'('#skF_10','#skF_7')
      | ~ r2_hidden(D_41,'#skF_8')
      | k2_relat_1('#skF_10') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_318,c_68061])).

tff(c_68246,plain,(
    ! [D_1275] :
      ( k1_funct_1('#skF_10',D_1275) != '#skF_3'('#skF_10','#skF_7')
      | ~ r2_hidden(D_1275,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_65266,c_68064])).

tff(c_68716,plain,(
    ! [C_1285] :
      ( k1_funct_1('#skF_10','#skF_4'('#skF_10',k2_relat_1('#skF_10'),C_1285)) != '#skF_3'('#skF_10','#skF_7')
      | ~ r2_hidden(C_1285,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_333,c_68246])).

tff(c_68747,plain,(
    ! [C_42] :
      ( C_42 != '#skF_3'('#skF_10','#skF_7')
      | ~ r2_hidden(C_42,k2_relat_1('#skF_10'))
      | ~ r2_hidden(C_42,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68716])).

tff(c_68757,plain,(
    ! [C_1286] :
      ( C_1286 != '#skF_3'('#skF_10','#skF_7')
      | ~ r2_hidden(C_1286,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_68747])).

tff(c_68908,plain,(
    ! [F_1287] :
      ( F_1287 != '#skF_3'('#skF_10','#skF_7')
      | ~ r2_hidden(F_1287,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_440,c_68757])).

tff(c_69606,plain,(
    ! [A_1315] :
      ( '#skF_3'(A_1315,'#skF_7') != '#skF_3'('#skF_10','#skF_7')
      | ~ r2_hidden('#skF_1'(A_1315,'#skF_7'),'#skF_7')
      | k2_relat_1(A_1315) = '#skF_7'
      | ~ v1_funct_1(A_1315)
      | ~ v1_relat_1(A_1315) ) ),
    inference(resolution,[status(thm)],[c_18,c_68908])).

tff(c_69613,plain,
    ( k2_relat_1('#skF_10') = '#skF_7'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_68029,c_69606])).

tff(c_69624,plain,(
    k2_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_66,c_69613])).

tff(c_69626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65266,c_69624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.47/13.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.47/13.63  
% 25.47/13.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.47/13.63  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5
% 25.47/13.63  
% 25.47/13.63  %Foreground sorts:
% 25.47/13.63  
% 25.47/13.63  
% 25.47/13.63  %Background operators:
% 25.47/13.63  
% 25.47/13.63  
% 25.47/13.63  %Foreground operators:
% 25.47/13.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 25.47/13.63  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 25.47/13.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 25.47/13.63  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 25.47/13.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 25.47/13.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.47/13.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.47/13.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.47/13.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 25.47/13.63  tff('#skF_7', type, '#skF_7': $i).
% 25.47/13.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 25.47/13.63  tff('#skF_10', type, '#skF_10': $i).
% 25.47/13.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 25.47/13.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 25.47/13.63  tff('#skF_9', type, '#skF_9': $i).
% 25.47/13.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 25.47/13.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.47/13.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 25.47/13.63  tff('#skF_8', type, '#skF_8': $i).
% 25.47/13.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.47/13.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 25.47/13.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 25.47/13.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.47/13.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 25.47/13.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 25.47/13.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 25.47/13.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 25.47/13.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.47/13.63  
% 25.68/13.66  tff(f_142, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) & (![E, F]: (((r2_hidden(E, B) & (k1_funct_1(D, E) = F)) => (r2_hidden(F, A) & (k1_funct_1(C, F) = E))) & ((r2_hidden(F, A) & (k1_funct_1(C, F) = E)) => (r2_hidden(E, B) & (k1_funct_1(D, E) = F)))))) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_2)).
% 25.68/13.66  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 25.68/13.66  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 25.68/13.66  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 25.68/13.66  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 25.68/13.66  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 25.68/13.66  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 25.68/13.66  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((((v2_funct_1(A) & (k1_relat_1(A) = k2_relat_1(B))) & (k2_relat_1(A) = k1_relat_1(B))) & (![C, D]: ((r2_hidden(C, k1_relat_1(A)) & r2_hidden(D, k1_relat_1(B))) => ((k1_funct_1(A, C) = D) <=> (k1_funct_1(B, D) = C))))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_1)).
% 25.68/13.66  tff(c_52, plain, (k2_funct_1('#skF_9')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.68/13.66  tff(c_68, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_87, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 25.68/13.66  tff(c_93, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_68, c_87])).
% 25.68/13.66  tff(c_99, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_93])).
% 25.68/13.66  tff(c_72, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_58, plain, (v2_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_54, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_70, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_151, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 25.68/13.66  tff(c_159, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_68, c_151])).
% 25.68/13.66  tff(c_308, plain, (![B_112, A_113, C_114]: (k1_xboole_0=B_112 | k1_relset_1(A_113, B_112, C_114)=A_113 | ~v1_funct_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 25.68/13.66  tff(c_314, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_68, c_308])).
% 25.68/13.66  tff(c_321, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_159, c_314])).
% 25.68/13.66  tff(c_322, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_54, c_321])).
% 25.68/13.66  tff(c_60, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_133, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 25.68/13.66  tff(c_139, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_68, c_133])).
% 25.68/13.66  tff(c_142, plain, (k2_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_139])).
% 25.68/13.66  tff(c_62, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_90, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_87])).
% 25.68/13.66  tff(c_96, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_90])).
% 25.68/13.66  tff(c_66, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_56, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_64, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_158, plain, (k1_relset_1('#skF_8', '#skF_7', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_62, c_151])).
% 25.68/13.66  tff(c_311, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_8', '#skF_7', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_308])).
% 25.68/13.66  tff(c_317, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_158, c_311])).
% 25.68/13.66  tff(c_318, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_56, c_317])).
% 25.68/13.66  tff(c_347, plain, (![A_115, B_116]: (r2_hidden('#skF_2'(A_115, B_116), k1_relat_1(A_115)) | r2_hidden('#skF_3'(A_115, B_116), B_116) | k2_relat_1(A_115)=B_116 | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.68/13.66  tff(c_353, plain, (![B_116]: (r2_hidden('#skF_2'('#skF_10', B_116), '#skF_8') | r2_hidden('#skF_3'('#skF_10', B_116), B_116) | k2_relat_1('#skF_10')=B_116 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_318, c_347])).
% 25.68/13.66  tff(c_357, plain, (![B_116]: (r2_hidden('#skF_2'('#skF_10', B_116), '#skF_8') | r2_hidden('#skF_3'('#skF_10', B_116), B_116) | k2_relat_1('#skF_10')=B_116)), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_353])).
% 25.68/13.66  tff(c_80, plain, (![F_72]: (r2_hidden(k1_funct_1('#skF_9', F_72), '#skF_8') | ~r2_hidden(F_72, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_78, plain, (![F_72]: (k1_funct_1('#skF_10', k1_funct_1('#skF_9', F_72))=F_72 | ~r2_hidden(F_72, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_59206, plain, (![A_1013, B_1014, D_1015]: (r2_hidden('#skF_2'(A_1013, B_1014), k1_relat_1(A_1013)) | k1_funct_1(A_1013, D_1015)!='#skF_3'(A_1013, B_1014) | ~r2_hidden(D_1015, k1_relat_1(A_1013)) | k2_relat_1(A_1013)=B_1014 | ~v1_funct_1(A_1013) | ~v1_relat_1(A_1013))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.68/13.66  tff(c_59216, plain, (![B_1014, F_72]: (r2_hidden('#skF_2'('#skF_10', B_1014), k1_relat_1('#skF_10')) | F_72!='#skF_3'('#skF_10', B_1014) | ~r2_hidden(k1_funct_1('#skF_9', F_72), k1_relat_1('#skF_10')) | k2_relat_1('#skF_10')=B_1014 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(F_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_59206])).
% 25.68/13.66  tff(c_59224, plain, (![B_1014, F_72]: (r2_hidden('#skF_2'('#skF_10', B_1014), '#skF_8') | F_72!='#skF_3'('#skF_10', B_1014) | ~r2_hidden(k1_funct_1('#skF_9', F_72), '#skF_8') | k2_relat_1('#skF_10')=B_1014 | ~r2_hidden(F_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_318, c_318, c_59216])).
% 25.68/13.66  tff(c_60169, plain, (![B_1052]: (r2_hidden('#skF_2'('#skF_10', B_1052), '#skF_8') | ~r2_hidden(k1_funct_1('#skF_9', '#skF_3'('#skF_10', B_1052)), '#skF_8') | k2_relat_1('#skF_10')=B_1052 | ~r2_hidden('#skF_3'('#skF_10', B_1052), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_59224])).
% 25.68/13.66  tff(c_60388, plain, (![B_1055]: (r2_hidden('#skF_2'('#skF_10', B_1055), '#skF_8') | k2_relat_1('#skF_10')=B_1055 | ~r2_hidden('#skF_3'('#skF_10', B_1055), '#skF_7'))), inference(resolution, [status(thm)], [c_80, c_60169])).
% 25.68/13.66  tff(c_60403, plain, (r2_hidden('#skF_2'('#skF_10', '#skF_7'), '#skF_8') | k2_relat_1('#skF_10')='#skF_7'), inference(resolution, [status(thm)], [c_357, c_60388])).
% 25.68/13.66  tff(c_60410, plain, (k2_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_60403])).
% 25.68/13.66  tff(c_59617, plain, (![A_1028, B_1029]: (r2_hidden('#skF_6'(A_1028, B_1029), k1_relat_1(B_1029)) | k2_funct_1(A_1028)=B_1029 | k2_relat_1(A_1028)!=k1_relat_1(B_1029) | k2_relat_1(B_1029)!=k1_relat_1(A_1028) | ~v2_funct_1(A_1028) | ~v1_funct_1(B_1029) | ~v1_relat_1(B_1029) | ~v1_funct_1(A_1028) | ~v1_relat_1(A_1028))), inference(cnfTransformation, [status(thm)], [f_75])).
% 25.68/13.66  tff(c_59623, plain, (![A_1028]: (r2_hidden('#skF_6'(A_1028, '#skF_10'), '#skF_8') | k2_funct_1(A_1028)='#skF_10' | k2_relat_1(A_1028)!=k1_relat_1('#skF_10') | k2_relat_1('#skF_10')!=k1_relat_1(A_1028) | ~v2_funct_1(A_1028) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~v1_funct_1(A_1028) | ~v1_relat_1(A_1028))), inference(superposition, [status(thm), theory('equality')], [c_318, c_59617])).
% 25.68/13.66  tff(c_59627, plain, (![A_1028]: (r2_hidden('#skF_6'(A_1028, '#skF_10'), '#skF_8') | k2_funct_1(A_1028)='#skF_10' | k2_relat_1(A_1028)!='#skF_8' | k2_relat_1('#skF_10')!=k1_relat_1(A_1028) | ~v2_funct_1(A_1028) | ~v1_funct_1(A_1028) | ~v1_relat_1(A_1028))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_318, c_59623])).
% 25.68/13.66  tff(c_65249, plain, (![A_1184]: (r2_hidden('#skF_6'(A_1184, '#skF_10'), '#skF_8') | k2_funct_1(A_1184)='#skF_10' | k2_relat_1(A_1184)!='#skF_8' | k1_relat_1(A_1184)!='#skF_7' | ~v2_funct_1(A_1184) | ~v1_funct_1(A_1184) | ~v1_relat_1(A_1184))), inference(demodulation, [status(thm), theory('equality')], [c_60410, c_59627])).
% 25.68/13.66  tff(c_59770, plain, (![A_1036, B_1037]: (r2_hidden('#skF_5'(A_1036, B_1037), k1_relat_1(A_1036)) | k2_funct_1(A_1036)=B_1037 | k2_relat_1(A_1036)!=k1_relat_1(B_1037) | k2_relat_1(B_1037)!=k1_relat_1(A_1036) | ~v2_funct_1(A_1036) | ~v1_funct_1(B_1037) | ~v1_relat_1(B_1037) | ~v1_funct_1(A_1036) | ~v1_relat_1(A_1036))), inference(cnfTransformation, [status(thm)], [f_75])).
% 25.68/13.66  tff(c_59773, plain, (![B_1037]: (r2_hidden('#skF_5'('#skF_9', B_1037), '#skF_7') | k2_funct_1('#skF_9')=B_1037 | k2_relat_1('#skF_9')!=k1_relat_1(B_1037) | k2_relat_1(B_1037)!=k1_relat_1('#skF_9') | ~v2_funct_1('#skF_9') | ~v1_funct_1(B_1037) | ~v1_relat_1(B_1037) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_59770])).
% 25.68/13.66  tff(c_59778, plain, (![B_1037]: (r2_hidden('#skF_5'('#skF_9', B_1037), '#skF_7') | k2_funct_1('#skF_9')=B_1037 | k1_relat_1(B_1037)!='#skF_8' | k2_relat_1(B_1037)!='#skF_7' | ~v1_funct_1(B_1037) | ~v1_relat_1(B_1037))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_72, c_58, c_322, c_142, c_59773])).
% 25.68/13.66  tff(c_60174, plain, (![A_1053, B_1054]: (k1_funct_1(A_1053, '#skF_5'(A_1053, B_1054))='#skF_6'(A_1053, B_1054) | k1_funct_1(B_1054, '#skF_6'(A_1053, B_1054))='#skF_5'(A_1053, B_1054) | k2_funct_1(A_1053)=B_1054 | k2_relat_1(A_1053)!=k1_relat_1(B_1054) | k2_relat_1(B_1054)!=k1_relat_1(A_1053) | ~v2_funct_1(A_1053) | ~v1_funct_1(B_1054) | ~v1_relat_1(B_1054) | ~v1_funct_1(A_1053) | ~v1_relat_1(A_1053))), inference(cnfTransformation, [status(thm)], [f_75])).
% 25.68/13.66  tff(c_60244, plain, (![B_1054]: (r2_hidden('#skF_6'('#skF_9', B_1054), '#skF_8') | ~r2_hidden('#skF_5'('#skF_9', B_1054), '#skF_7') | k1_funct_1(B_1054, '#skF_6'('#skF_9', B_1054))='#skF_5'('#skF_9', B_1054) | k2_funct_1('#skF_9')=B_1054 | k2_relat_1('#skF_9')!=k1_relat_1(B_1054) | k2_relat_1(B_1054)!=k1_relat_1('#skF_9') | ~v2_funct_1('#skF_9') | ~v1_funct_1(B_1054) | ~v1_relat_1(B_1054) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_60174, c_80])).
% 25.68/13.66  tff(c_60353, plain, (![B_1054]: (r2_hidden('#skF_6'('#skF_9', B_1054), '#skF_8') | ~r2_hidden('#skF_5'('#skF_9', B_1054), '#skF_7') | k1_funct_1(B_1054, '#skF_6'('#skF_9', B_1054))='#skF_5'('#skF_9', B_1054) | k2_funct_1('#skF_9')=B_1054 | k1_relat_1(B_1054)!='#skF_8' | k2_relat_1(B_1054)!='#skF_7' | ~v1_funct_1(B_1054) | ~v1_relat_1(B_1054))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_72, c_58, c_322, c_142, c_60244])).
% 25.68/13.66  tff(c_74, plain, (![E_71]: (k1_funct_1('#skF_9', k1_funct_1('#skF_10', E_71))=E_71 | ~r2_hidden(E_71, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_60308, plain, (![A_1053]: (k1_funct_1('#skF_9', '#skF_5'(A_1053, '#skF_10'))='#skF_6'(A_1053, '#skF_10') | ~r2_hidden('#skF_6'(A_1053, '#skF_10'), '#skF_8') | k1_funct_1(A_1053, '#skF_5'(A_1053, '#skF_10'))='#skF_6'(A_1053, '#skF_10') | k2_funct_1(A_1053)='#skF_10' | k2_relat_1(A_1053)!=k1_relat_1('#skF_10') | k2_relat_1('#skF_10')!=k1_relat_1(A_1053) | ~v2_funct_1(A_1053) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~v1_funct_1(A_1053) | ~v1_relat_1(A_1053))), inference(superposition, [status(thm), theory('equality')], [c_60174, c_74])).
% 25.68/13.66  tff(c_60381, plain, (![A_1053]: (k1_funct_1('#skF_9', '#skF_5'(A_1053, '#skF_10'))='#skF_6'(A_1053, '#skF_10') | ~r2_hidden('#skF_6'(A_1053, '#skF_10'), '#skF_8') | k1_funct_1(A_1053, '#skF_5'(A_1053, '#skF_10'))='#skF_6'(A_1053, '#skF_10') | k2_funct_1(A_1053)='#skF_10' | k2_relat_1(A_1053)!='#skF_8' | k2_relat_1('#skF_10')!=k1_relat_1(A_1053) | ~v2_funct_1(A_1053) | ~v1_funct_1(A_1053) | ~v1_relat_1(A_1053))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_318, c_60308])).
% 25.68/13.66  tff(c_62465, plain, (![A_1116]: (k1_funct_1('#skF_9', '#skF_5'(A_1116, '#skF_10'))='#skF_6'(A_1116, '#skF_10') | ~r2_hidden('#skF_6'(A_1116, '#skF_10'), '#skF_8') | k1_funct_1(A_1116, '#skF_5'(A_1116, '#skF_10'))='#skF_6'(A_1116, '#skF_10') | k2_funct_1(A_1116)='#skF_10' | k2_relat_1(A_1116)!='#skF_8' | k1_relat_1(A_1116)!='#skF_7' | ~v2_funct_1(A_1116) | ~v1_funct_1(A_1116) | ~v1_relat_1(A_1116))), inference(demodulation, [status(thm), theory('equality')], [c_60410, c_60381])).
% 25.68/13.66  tff(c_62468, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_10'))='#skF_6'('#skF_9', '#skF_10') | k2_relat_1('#skF_9')!='#skF_8' | k1_relat_1('#skF_9')!='#skF_7' | ~v2_funct_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden('#skF_5'('#skF_9', '#skF_10'), '#skF_7') | k1_funct_1('#skF_10', '#skF_6'('#skF_9', '#skF_10'))='#skF_5'('#skF_9', '#skF_10') | k2_funct_1('#skF_9')='#skF_10' | k1_relat_1('#skF_10')!='#skF_8' | k2_relat_1('#skF_10')!='#skF_7' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_60353, c_62465])).
% 25.68/13.66  tff(c_62471, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_10'))='#skF_6'('#skF_9', '#skF_10') | ~r2_hidden('#skF_5'('#skF_9', '#skF_10'), '#skF_7') | k1_funct_1('#skF_10', '#skF_6'('#skF_9', '#skF_10'))='#skF_5'('#skF_9', '#skF_10') | k2_funct_1('#skF_9')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_60410, c_318, c_99, c_72, c_58, c_322, c_142, c_62468])).
% 25.68/13.66  tff(c_62472, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_10'))='#skF_6'('#skF_9', '#skF_10') | ~r2_hidden('#skF_5'('#skF_9', '#skF_10'), '#skF_7') | k1_funct_1('#skF_10', '#skF_6'('#skF_9', '#skF_10'))='#skF_5'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_52, c_62471])).
% 25.68/13.66  tff(c_62673, plain, (~r2_hidden('#skF_5'('#skF_9', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_62472])).
% 25.68/13.66  tff(c_62676, plain, (k2_funct_1('#skF_9')='#skF_10' | k1_relat_1('#skF_10')!='#skF_8' | k2_relat_1('#skF_10')!='#skF_7' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_59778, c_62673])).
% 25.68/13.66  tff(c_62679, plain, (k2_funct_1('#skF_9')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_60410, c_318, c_62676])).
% 25.68/13.66  tff(c_62681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_62679])).
% 25.68/13.66  tff(c_62683, plain, (r2_hidden('#skF_5'('#skF_9', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_62472])).
% 25.68/13.66  tff(c_10, plain, (![A_6, C_42]: (r2_hidden('#skF_4'(A_6, k2_relat_1(A_6), C_42), k1_relat_1(A_6)) | ~r2_hidden(C_42, k2_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.68/13.66  tff(c_329, plain, (![C_42]: (r2_hidden('#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_42), '#skF_8') | ~r2_hidden(C_42, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_318, c_10])).
% 25.68/13.66  tff(c_333, plain, (![C_42]: (r2_hidden('#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_42), '#skF_8') | ~r2_hidden(C_42, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_329])).
% 25.68/13.66  tff(c_207, plain, (![A_102, C_103]: (k1_funct_1(A_102, '#skF_4'(A_102, k2_relat_1(A_102), C_103))=C_103 | ~r2_hidden(C_103, k2_relat_1(A_102)) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.68/13.66  tff(c_233, plain, (![C_103]: ('#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_103)=k1_funct_1('#skF_9', C_103) | ~r2_hidden('#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_103), '#skF_8') | ~r2_hidden(C_103, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_74])).
% 25.68/13.66  tff(c_59135, plain, (![C_1010]: ('#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_1010)=k1_funct_1('#skF_9', C_1010) | ~r2_hidden('#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_1010), '#skF_8') | ~r2_hidden(C_1010, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_233])).
% 25.68/13.66  tff(c_59139, plain, (![C_42]: ('#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_42)=k1_funct_1('#skF_9', C_42) | ~r2_hidden(C_42, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_333, c_59135])).
% 25.68/13.66  tff(c_60428, plain, (![C_42]: (k1_funct_1('#skF_9', C_42)='#skF_4'('#skF_10', '#skF_7', C_42) | ~r2_hidden(C_42, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_60410, c_60410, c_59139])).
% 25.68/13.66  tff(c_62693, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_10'))='#skF_4'('#skF_10', '#skF_7', '#skF_5'('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_62683, c_60428])).
% 25.68/13.66  tff(c_60232, plain, (![B_1054]: (k1_funct_1('#skF_10', '#skF_6'('#skF_9', B_1054))='#skF_5'('#skF_9', B_1054) | ~r2_hidden('#skF_5'('#skF_9', B_1054), '#skF_7') | k1_funct_1(B_1054, '#skF_6'('#skF_9', B_1054))='#skF_5'('#skF_9', B_1054) | k2_funct_1('#skF_9')=B_1054 | k2_relat_1('#skF_9')!=k1_relat_1(B_1054) | k2_relat_1(B_1054)!=k1_relat_1('#skF_9') | ~v2_funct_1('#skF_9') | ~v1_funct_1(B_1054) | ~v1_relat_1(B_1054) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_60174, c_78])).
% 25.68/13.66  tff(c_60347, plain, (![B_1054]: (k1_funct_1('#skF_10', '#skF_6'('#skF_9', B_1054))='#skF_5'('#skF_9', B_1054) | ~r2_hidden('#skF_5'('#skF_9', B_1054), '#skF_7') | k1_funct_1(B_1054, '#skF_6'('#skF_9', B_1054))='#skF_5'('#skF_9', B_1054) | k2_funct_1('#skF_9')=B_1054 | k1_relat_1(B_1054)!='#skF_8' | k2_relat_1(B_1054)!='#skF_7' | ~v1_funct_1(B_1054) | ~v1_relat_1(B_1054))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_72, c_58, c_322, c_142, c_60232])).
% 25.68/13.66  tff(c_62685, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_9', '#skF_10'))='#skF_5'('#skF_9', '#skF_10') | k2_funct_1('#skF_9')='#skF_10' | k1_relat_1('#skF_10')!='#skF_8' | k2_relat_1('#skF_10')!='#skF_7' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_62683, c_60347])).
% 25.68/13.66  tff(c_62691, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_9', '#skF_10'))='#skF_5'('#skF_9', '#skF_10') | k2_funct_1('#skF_9')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_60410, c_318, c_62685])).
% 25.68/13.66  tff(c_62692, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_9', '#skF_10'))='#skF_5'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_52, c_62691])).
% 25.68/13.66  tff(c_28, plain, (![B_52, A_46]: (k1_funct_1(B_52, '#skF_6'(A_46, B_52))!='#skF_5'(A_46, B_52) | k1_funct_1(A_46, '#skF_5'(A_46, B_52))!='#skF_6'(A_46, B_52) | k2_funct_1(A_46)=B_52 | k2_relat_1(A_46)!=k1_relat_1(B_52) | k2_relat_1(B_52)!=k1_relat_1(A_46) | ~v2_funct_1(A_46) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 25.68/13.66  tff(c_62709, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_10'))!='#skF_6'('#skF_9', '#skF_10') | k2_funct_1('#skF_9')='#skF_10' | k2_relat_1('#skF_9')!=k1_relat_1('#skF_10') | k2_relat_1('#skF_10')!=k1_relat_1('#skF_9') | ~v2_funct_1('#skF_9') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_62692, c_28])).
% 25.68/13.66  tff(c_62743, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_10'))!='#skF_6'('#skF_9', '#skF_10') | k2_funct_1('#skF_9')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_72, c_96, c_66, c_58, c_322, c_60410, c_142, c_318, c_62709])).
% 25.68/13.66  tff(c_62744, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_10'))!='#skF_6'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_52, c_62743])).
% 25.68/13.66  tff(c_62761, plain, ('#skF_4'('#skF_10', '#skF_7', '#skF_5'('#skF_9', '#skF_10'))!='#skF_6'('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_62693, c_62744])).
% 25.68/13.66  tff(c_62725, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_10'))='#skF_6'('#skF_9', '#skF_10') | ~r2_hidden('#skF_6'('#skF_9', '#skF_10'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62692, c_74])).
% 25.68/13.66  tff(c_62817, plain, ('#skF_4'('#skF_10', '#skF_7', '#skF_5'('#skF_9', '#skF_10'))='#skF_6'('#skF_9', '#skF_10') | ~r2_hidden('#skF_6'('#skF_9', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62693, c_62725])).
% 25.68/13.66  tff(c_62818, plain, (~r2_hidden('#skF_6'('#skF_9', '#skF_10'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_62761, c_62817])).
% 25.68/13.66  tff(c_65252, plain, (k2_funct_1('#skF_9')='#skF_10' | k2_relat_1('#skF_9')!='#skF_8' | k1_relat_1('#skF_9')!='#skF_7' | ~v2_funct_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_65249, c_62818])).
% 25.68/13.66  tff(c_65262, plain, (k2_funct_1('#skF_9')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_72, c_58, c_322, c_142, c_65252])).
% 25.68/13.66  tff(c_65264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_65262])).
% 25.68/13.66  tff(c_65266, plain, (k2_relat_1('#skF_10')!='#skF_7'), inference(splitRight, [status(thm)], [c_60403])).
% 25.68/13.66  tff(c_65265, plain, (r2_hidden('#skF_2'('#skF_10', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_60403])).
% 25.68/13.66  tff(c_341, plain, (![C_42]: (r2_hidden('#skF_4'('#skF_9', k2_relat_1('#skF_9'), C_42), '#skF_7') | ~r2_hidden(C_42, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_10])).
% 25.68/13.66  tff(c_366, plain, (![C_117]: (r2_hidden('#skF_4'('#skF_9', '#skF_8', C_117), '#skF_7') | ~r2_hidden(C_117, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_72, c_142, c_142, c_341])).
% 25.68/13.66  tff(c_229, plain, (![C_103]: ('#skF_4'('#skF_9', k2_relat_1('#skF_9'), C_103)=k1_funct_1('#skF_10', C_103) | ~r2_hidden('#skF_4'('#skF_9', k2_relat_1('#skF_9'), C_103), '#skF_7') | ~r2_hidden(C_103, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_78])).
% 25.68/13.66  tff(c_256, plain, (![C_103]: (k1_funct_1('#skF_10', C_103)='#skF_4'('#skF_9', '#skF_8', C_103) | ~r2_hidden('#skF_4'('#skF_9', '#skF_8', C_103), '#skF_7') | ~r2_hidden(C_103, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_72, c_142, c_142, c_142, c_229])).
% 25.68/13.66  tff(c_370, plain, (![C_117]: (k1_funct_1('#skF_10', C_117)='#skF_4'('#skF_9', '#skF_8', C_117) | ~r2_hidden(C_117, '#skF_8'))), inference(resolution, [status(thm)], [c_366, c_256])).
% 25.68/13.66  tff(c_65270, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_10', '#skF_7'))='#skF_4'('#skF_9', '#skF_8', '#skF_2'('#skF_10', '#skF_7'))), inference(resolution, [status(thm)], [c_65265, c_370])).
% 25.68/13.66  tff(c_20, plain, (![A_6, B_28]: (k1_funct_1(A_6, '#skF_2'(A_6, B_28))='#skF_1'(A_6, B_28) | r2_hidden('#skF_3'(A_6, B_28), B_28) | k2_relat_1(A_6)=B_28 | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.68/13.66  tff(c_59401, plain, (![A_1023, B_1024, D_1025]: (k1_funct_1(A_1023, '#skF_2'(A_1023, B_1024))='#skF_1'(A_1023, B_1024) | k1_funct_1(A_1023, D_1025)!='#skF_3'(A_1023, B_1024) | ~r2_hidden(D_1025, k1_relat_1(A_1023)) | k2_relat_1(A_1023)=B_1024 | ~v1_funct_1(A_1023) | ~v1_relat_1(A_1023))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.68/13.66  tff(c_59413, plain, (![B_1024, F_72]: (k1_funct_1('#skF_10', '#skF_2'('#skF_10', B_1024))='#skF_1'('#skF_10', B_1024) | F_72!='#skF_3'('#skF_10', B_1024) | ~r2_hidden(k1_funct_1('#skF_9', F_72), k1_relat_1('#skF_10')) | k2_relat_1('#skF_10')=B_1024 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(F_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_59401])).
% 25.68/13.66  tff(c_59423, plain, (![B_1024, F_72]: (k1_funct_1('#skF_10', '#skF_2'('#skF_10', B_1024))='#skF_1'('#skF_10', B_1024) | F_72!='#skF_3'('#skF_10', B_1024) | ~r2_hidden(k1_funct_1('#skF_9', F_72), '#skF_8') | k2_relat_1('#skF_10')=B_1024 | ~r2_hidden(F_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_318, c_59413])).
% 25.68/13.66  tff(c_67966, plain, (![B_1268]: (k1_funct_1('#skF_10', '#skF_2'('#skF_10', B_1268))='#skF_1'('#skF_10', B_1268) | ~r2_hidden(k1_funct_1('#skF_9', '#skF_3'('#skF_10', B_1268)), '#skF_8') | k2_relat_1('#skF_10')=B_1268 | ~r2_hidden('#skF_3'('#skF_10', B_1268), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_59423])).
% 25.68/13.66  tff(c_67971, plain, (![B_1269]: (k1_funct_1('#skF_10', '#skF_2'('#skF_10', B_1269))='#skF_1'('#skF_10', B_1269) | k2_relat_1('#skF_10')=B_1269 | ~r2_hidden('#skF_3'('#skF_10', B_1269), '#skF_7'))), inference(resolution, [status(thm)], [c_80, c_67966])).
% 25.68/13.66  tff(c_67995, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_10', '#skF_7'))='#skF_1'('#skF_10', '#skF_7') | k2_relat_1('#skF_10')='#skF_7' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_20, c_67971])).
% 25.68/13.66  tff(c_68014, plain, ('#skF_4'('#skF_9', '#skF_8', '#skF_2'('#skF_10', '#skF_7'))='#skF_1'('#skF_10', '#skF_7') | k2_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_65270, c_67995])).
% 25.68/13.66  tff(c_68015, plain, ('#skF_4'('#skF_9', '#skF_8', '#skF_2'('#skF_10', '#skF_7'))='#skF_1'('#skF_10', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_65266, c_68014])).
% 25.68/13.66  tff(c_76, plain, (![E_71]: (r2_hidden(k1_funct_1('#skF_10', E_71), '#skF_7') | ~r2_hidden(E_71, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 25.68/13.66  tff(c_65303, plain, (r2_hidden('#skF_4'('#skF_9', '#skF_8', '#skF_2'('#skF_10', '#skF_7')), '#skF_7') | ~r2_hidden('#skF_2'('#skF_10', '#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_65270, c_76])).
% 25.68/13.66  tff(c_65328, plain, (r2_hidden('#skF_4'('#skF_9', '#skF_8', '#skF_2'('#skF_10', '#skF_7')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_65265, c_65303])).
% 25.68/13.66  tff(c_68029, plain, (r2_hidden('#skF_1'('#skF_10', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68015, c_65328])).
% 25.68/13.66  tff(c_18, plain, (![A_6, B_28]: (~r2_hidden('#skF_1'(A_6, B_28), B_28) | r2_hidden('#skF_3'(A_6, B_28), B_28) | k2_relat_1(A_6)=B_28 | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.68/13.66  tff(c_169, plain, (![A_88, D_89]: (r2_hidden(k1_funct_1(A_88, D_89), k2_relat_1(A_88)) | ~r2_hidden(D_89, k1_relat_1(A_88)) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.68/13.66  tff(c_175, plain, (![F_72]: (r2_hidden(F_72, k2_relat_1('#skF_10')) | ~r2_hidden(k1_funct_1('#skF_9', F_72), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(F_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_169])).
% 25.68/13.66  tff(c_182, plain, (![F_72]: (r2_hidden(F_72, k2_relat_1('#skF_10')) | ~r2_hidden(k1_funct_1('#skF_9', F_72), k1_relat_1('#skF_10')) | ~r2_hidden(F_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_175])).
% 25.68/13.66  tff(c_424, plain, (![F_122]: (r2_hidden(F_122, k2_relat_1('#skF_10')) | ~r2_hidden(k1_funct_1('#skF_9', F_122), '#skF_8') | ~r2_hidden(F_122, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_182])).
% 25.68/13.66  tff(c_440, plain, (![F_72]: (r2_hidden(F_72, k2_relat_1('#skF_10')) | ~r2_hidden(F_72, '#skF_7'))), inference(resolution, [status(thm)], [c_80, c_424])).
% 25.68/13.66  tff(c_8, plain, (![A_6, C_42]: (k1_funct_1(A_6, '#skF_4'(A_6, k2_relat_1(A_6), C_42))=C_42 | ~r2_hidden(C_42, k2_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.68/13.66  tff(c_12, plain, (![A_6, B_28, D_41]: (~r2_hidden('#skF_1'(A_6, B_28), B_28) | k1_funct_1(A_6, D_41)!='#skF_3'(A_6, B_28) | ~r2_hidden(D_41, k1_relat_1(A_6)) | k2_relat_1(A_6)=B_28 | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 25.68/13.66  tff(c_68061, plain, (![D_41]: (k1_funct_1('#skF_10', D_41)!='#skF_3'('#skF_10', '#skF_7') | ~r2_hidden(D_41, k1_relat_1('#skF_10')) | k2_relat_1('#skF_10')='#skF_7' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_68029, c_12])).
% 25.68/13.66  tff(c_68064, plain, (![D_41]: (k1_funct_1('#skF_10', D_41)!='#skF_3'('#skF_10', '#skF_7') | ~r2_hidden(D_41, '#skF_8') | k2_relat_1('#skF_10')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_318, c_68061])).
% 25.68/13.66  tff(c_68246, plain, (![D_1275]: (k1_funct_1('#skF_10', D_1275)!='#skF_3'('#skF_10', '#skF_7') | ~r2_hidden(D_1275, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_65266, c_68064])).
% 25.68/13.66  tff(c_68716, plain, (![C_1285]: (k1_funct_1('#skF_10', '#skF_4'('#skF_10', k2_relat_1('#skF_10'), C_1285))!='#skF_3'('#skF_10', '#skF_7') | ~r2_hidden(C_1285, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_333, c_68246])).
% 25.68/13.66  tff(c_68747, plain, (![C_42]: (C_42!='#skF_3'('#skF_10', '#skF_7') | ~r2_hidden(C_42, k2_relat_1('#skF_10')) | ~r2_hidden(C_42, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68716])).
% 25.68/13.66  tff(c_68757, plain, (![C_1286]: (C_1286!='#skF_3'('#skF_10', '#skF_7') | ~r2_hidden(C_1286, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_68747])).
% 25.68/13.66  tff(c_68908, plain, (![F_1287]: (F_1287!='#skF_3'('#skF_10', '#skF_7') | ~r2_hidden(F_1287, '#skF_7'))), inference(resolution, [status(thm)], [c_440, c_68757])).
% 25.68/13.66  tff(c_69606, plain, (![A_1315]: ('#skF_3'(A_1315, '#skF_7')!='#skF_3'('#skF_10', '#skF_7') | ~r2_hidden('#skF_1'(A_1315, '#skF_7'), '#skF_7') | k2_relat_1(A_1315)='#skF_7' | ~v1_funct_1(A_1315) | ~v1_relat_1(A_1315))), inference(resolution, [status(thm)], [c_18, c_68908])).
% 25.68/13.66  tff(c_69613, plain, (k2_relat_1('#skF_10')='#skF_7' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_68029, c_69606])).
% 25.68/13.66  tff(c_69624, plain, (k2_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_66, c_69613])).
% 25.68/13.66  tff(c_69626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65266, c_69624])).
% 25.68/13.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.68/13.66  
% 25.68/13.66  Inference rules
% 25.68/13.66  ----------------------
% 25.68/13.66  #Ref     : 34
% 25.68/13.66  #Sup     : 17610
% 25.68/13.66  #Fact    : 6
% 25.68/13.66  #Define  : 0
% 25.68/13.66  #Split   : 51
% 25.68/13.66  #Chain   : 0
% 25.68/13.66  #Close   : 0
% 25.68/13.66  
% 25.68/13.66  Ordering : KBO
% 25.68/13.66  
% 25.68/13.66  Simplification rules
% 25.68/13.66  ----------------------
% 25.68/13.66  #Subsume      : 4564
% 25.68/13.66  #Demod        : 13523
% 25.68/13.66  #Tautology    : 2763
% 25.68/13.66  #SimpNegUnit  : 520
% 25.68/13.66  #BackRed      : 80
% 25.68/13.66  
% 25.68/13.66  #Partial instantiations: 0
% 25.68/13.66  #Strategies tried      : 1
% 25.68/13.66  
% 25.68/13.66  Timing (in seconds)
% 25.68/13.66  ----------------------
% 25.68/13.66  Preprocessing        : 0.37
% 25.68/13.66  Parsing              : 0.18
% 25.68/13.66  CNF conversion       : 0.03
% 25.68/13.66  Main loop            : 12.50
% 25.68/13.66  Inferencing          : 2.65
% 25.68/13.66  Reduction            : 3.56
% 25.68/13.66  Demodulation         : 2.61
% 25.68/13.66  BG Simplification    : 0.37
% 25.68/13.66  Subsumption          : 5.27
% 25.68/13.66  Abstraction          : 0.46
% 25.68/13.66  MUC search           : 0.00
% 25.68/13.66  Cooper               : 0.00
% 25.68/13.66  Total                : 12.92
% 25.68/13.66  Index Insertion      : 0.00
% 25.68/13.67  Index Deletion       : 0.00
% 25.68/13.67  Index Matching       : 0.00
% 25.68/13.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
