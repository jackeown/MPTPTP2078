%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:30 EST 2020

% Result     : Theorem 41.65s
% Output     : CNFRefutation 41.77s
% Verified   : 
% Statistics : Number of formulae       :  132 (1208 expanded)
%              Number of leaves         :   46 ( 430 expanded)
%              Depth                    :   18
%              Number of atoms          :  217 (3343 expanded)
%              Number of equality atoms :   59 (1072 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k3_tarski > k2_mcart_1 > k1_zfmisc_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_78,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3089,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( k7_relset_1(A_203,B_204,C_205,D_206) = k9_relat_1(C_205,D_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3115,plain,(
    ! [D_206] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_206) = k9_relat_1('#skF_10',D_206) ),
    inference(resolution,[status(thm)],[c_78,c_3089])).

tff(c_76,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_3184,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3115,c_127])).

tff(c_32,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_126,plain,(
    m1_subset_1('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_76,c_32])).

tff(c_3183,plain,(
    m1_subset_1('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3115,c_126])).

tff(c_128,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_139,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_128])).

tff(c_82,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3185,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3115,c_76])).

tff(c_5879,plain,(
    ! [A_259,B_260,C_261] :
      ( r2_hidden(k4_tarski('#skF_6'(A_259,B_260,C_261),A_259),C_261)
      | ~ r2_hidden(A_259,k9_relat_1(C_261,B_260))
      | ~ v1_relat_1(C_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,(
    ! [C_41,A_39,B_40] :
      ( k1_funct_1(C_41,A_39) = B_40
      | ~ r2_hidden(k4_tarski(A_39,B_40),C_41)
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_39481,plain,(
    ! [C_715,A_716,B_717] :
      ( k1_funct_1(C_715,'#skF_6'(A_716,B_717,C_715)) = A_716
      | ~ v1_funct_1(C_715)
      | ~ r2_hidden(A_716,k9_relat_1(C_715,B_717))
      | ~ v1_relat_1(C_715) ) ),
    inference(resolution,[status(thm)],[c_5879,c_48])).

tff(c_39546,plain,
    ( k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) = '#skF_11'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3185,c_39481])).

tff(c_39600,plain,(
    k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_82,c_39546])).

tff(c_80,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_808,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_824,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_808])).

tff(c_7571,plain,(
    ! [B_292,A_293,C_294] :
      ( k1_xboole_0 = B_292
      | k1_relset_1(A_293,B_292,C_294) = A_293
      | ~ v1_funct_2(C_294,A_293,B_292)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_293,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_7594,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_7571])).

tff(c_7605,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_824,c_7594])).

tff(c_7606,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_7605])).

tff(c_2666,plain,(
    ! [A_190,B_191,C_192] :
      ( r2_hidden('#skF_6'(A_190,B_191,C_192),k1_relat_1(C_192))
      | ~ r2_hidden(A_190,k9_relat_1(C_192,B_191))
      | ~ v1_relat_1(C_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24170,plain,(
    ! [A_531,B_532,C_533] :
      ( m1_subset_1('#skF_6'(A_531,B_532,C_533),k1_relat_1(C_533))
      | ~ r2_hidden(A_531,k9_relat_1(C_533,B_532))
      | ~ v1_relat_1(C_533) ) ),
    inference(resolution,[status(thm)],[c_2666,c_32])).

tff(c_24173,plain,(
    ! [A_531,B_532] :
      ( m1_subset_1('#skF_6'(A_531,B_532,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_531,k9_relat_1('#skF_10',B_532))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7606,c_24170])).

tff(c_198762,plain,(
    ! [A_1573,B_1574] :
      ( m1_subset_1('#skF_6'(A_1573,B_1574,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_1573,k9_relat_1('#skF_10',B_1574)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_24173])).

tff(c_199013,plain,(
    m1_subset_1('#skF_6'('#skF_11','#skF_9','#skF_10'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_3185,c_198762])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(A_30,B_31)
      | v1_xboole_0(B_31)
      | ~ m1_subset_1(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2519,plain,(
    ! [A_187,B_188,C_189] :
      ( r2_hidden('#skF_6'(A_187,B_188,C_189),B_188)
      | ~ r2_hidden(A_187,k9_relat_1(C_189,B_188))
      | ~ v1_relat_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_74,plain,(
    ! [F_62] :
      ( k1_funct_1('#skF_10',F_62) != '#skF_11'
      | ~ r2_hidden(F_62,'#skF_9')
      | ~ m1_subset_1(F_62,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2833,plain,(
    ! [A_195,C_196] :
      ( k1_funct_1('#skF_10','#skF_6'(A_195,'#skF_9',C_196)) != '#skF_11'
      | ~ m1_subset_1('#skF_6'(A_195,'#skF_9',C_196),'#skF_7')
      | ~ r2_hidden(A_195,k9_relat_1(C_196,'#skF_9'))
      | ~ v1_relat_1(C_196) ) ),
    inference(resolution,[status(thm)],[c_2519,c_74])).

tff(c_2887,plain,(
    ! [A_30,C_196] :
      ( k1_funct_1('#skF_10','#skF_6'(A_30,'#skF_9',C_196)) != '#skF_11'
      | ~ m1_subset_1('#skF_6'(A_30,'#skF_9',C_196),'#skF_7')
      | ~ v1_relat_1(C_196)
      | v1_xboole_0(k9_relat_1(C_196,'#skF_9'))
      | ~ m1_subset_1(A_30,k9_relat_1(C_196,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_34,c_2833])).

tff(c_199027,plain,
    ( k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) != '#skF_11'
    | ~ v1_relat_1('#skF_10')
    | v1_xboole_0(k9_relat_1('#skF_10','#skF_9'))
    | ~ m1_subset_1('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_199013,c_2887])).

tff(c_199033,plain,(
    v1_xboole_0(k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3183,c_139,c_39600,c_199027])).

tff(c_199035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3184,c_199033])).

tff(c_199036,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_7605])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_199102,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199036,c_6])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_83,C_84,B_85] :
      ( r2_hidden(k2_mcart_1(A_83),C_84)
      | ~ r2_hidden(A_83,k2_zfmisc_1(B_85,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_201221,plain,(
    ! [B_1627,C_1628] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1627,C_1628))),C_1628)
      | v1_xboole_0(k2_zfmisc_1(B_1627,C_1628)) ) ),
    inference(resolution,[status(thm)],[c_4,c_161])).

tff(c_317,plain,(
    ! [A_106,C_107] :
      ( r2_hidden('#skF_5'(A_106,k3_tarski(A_106),C_107),A_106)
      | ~ r2_hidden(C_107,k3_tarski(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_356,plain,(
    ! [A_108,C_109] :
      ( ~ v1_xboole_0(A_108)
      | ~ r2_hidden(C_109,k3_tarski(A_108)) ) ),
    inference(resolution,[status(thm)],[c_317,c_2])).

tff(c_383,plain,(
    ! [A_110] :
      ( ~ v1_xboole_0(A_110)
      | v1_xboole_0(k3_tarski(A_110)) ) ),
    inference(resolution,[status(thm)],[c_4,c_356])).

tff(c_109,plain,(
    ! [B_71,A_72] :
      ( ~ v1_xboole_0(B_71)
      | B_71 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_112,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_402,plain,(
    ! [A_111] :
      ( k3_tarski(A_111) = k1_xboole_0
      | ~ v1_xboole_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_383,c_112])).

tff(c_414,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_402])).

tff(c_354,plain,(
    ! [A_106,C_107] :
      ( ~ v1_xboole_0(A_106)
      | ~ r2_hidden(C_107,k3_tarski(A_106)) ) ),
    inference(resolution,[status(thm)],[c_317,c_2])).

tff(c_422,plain,(
    ! [C_107] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_107,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_354])).

tff(c_440,plain,(
    ! [C_107] : ~ r2_hidden(C_107,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_422])).

tff(c_199095,plain,(
    ! [C_107] : ~ r2_hidden(C_107,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199036,c_440])).

tff(c_201321,plain,(
    ! [B_1629] : v1_xboole_0(k2_zfmisc_1(B_1629,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_201221,c_199095])).

tff(c_199100,plain,(
    ! [A_72] :
      ( A_72 = '#skF_8'
      | ~ v1_xboole_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199036,c_112])).

tff(c_201356,plain,(
    ! [B_1629] : k2_zfmisc_1(B_1629,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_201321,c_199100])).

tff(c_201369,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201356,c_78])).

tff(c_64,plain,(
    ! [C_57,A_55] :
      ( k1_xboole_0 = C_57
      | ~ v1_funct_2(C_57,A_55,k1_xboole_0)
      | k1_xboole_0 = A_55
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_199072,plain,(
    ! [C_57,A_55] :
      ( C_57 = '#skF_8'
      | ~ v1_funct_2(C_57,A_55,'#skF_8')
      | A_55 = '#skF_8'
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,'#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199036,c_199036,c_199036,c_199036,c_64])).

tff(c_207394,plain,(
    ! [C_1742,A_1743] :
      ( C_1742 = '#skF_8'
      | ~ v1_funct_2(C_1742,A_1743,'#skF_8')
      | A_1743 = '#skF_8'
      | ~ m1_subset_1(C_1742,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201356,c_199072])).

tff(c_207398,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_8'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_207394])).

tff(c_207405,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201369,c_207398])).

tff(c_207406,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_207405])).

tff(c_199037,plain,(
    k1_relat_1('#skF_10') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7605])).

tff(c_207420,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207406,c_199037])).

tff(c_207430,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207406,c_824])).

tff(c_207433,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207406,c_80])).

tff(c_170,plain,(
    ! [A_86,B_87,C_88] :
      ( r2_hidden(k1_mcart_1(A_86),B_87)
      | ~ r2_hidden(A_86,k2_zfmisc_1(B_87,C_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_200953,plain,(
    ! [B_1616,C_1617] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1616,C_1617))),B_1616)
      | v1_xboole_0(k2_zfmisc_1(B_1616,C_1617)) ) ),
    inference(resolution,[status(thm)],[c_4,c_170])).

tff(c_201049,plain,(
    ! [C_1618] : v1_xboole_0(k2_zfmisc_1('#skF_8',C_1618)) ),
    inference(resolution,[status(thm)],[c_200953,c_199095])).

tff(c_201078,plain,(
    ! [C_1618] : k2_zfmisc_1('#skF_8',C_1618) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_201049,c_199100])).

tff(c_70,plain,(
    ! [B_56,C_57] :
      ( k1_relset_1(k1_xboole_0,B_56,C_57) = k1_xboole_0
      | ~ v1_funct_2(C_57,k1_xboole_0,B_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_199067,plain,(
    ! [B_56,C_57] :
      ( k1_relset_1('#skF_8',B_56,C_57) = '#skF_8'
      | ~ v1_funct_2(C_57,'#skF_8',B_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_56))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199036,c_199036,c_199036,c_199036,c_70])).

tff(c_209834,plain,(
    ! [B_1795,C_1796] :
      ( k1_relset_1('#skF_8',B_1795,C_1796) = '#skF_8'
      | ~ v1_funct_2(C_1796,'#skF_8',B_1795)
      | ~ m1_subset_1(C_1796,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201078,c_199067])).

tff(c_209836,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_207433,c_209834])).

tff(c_209842,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201369,c_207430,c_209836])).

tff(c_209844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207420,c_209842])).

tff(c_209845,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_207405])).

tff(c_6202,plain,(
    ! [C_268,A_269,B_270] :
      ( ~ v1_xboole_0(C_268)
      | ~ r2_hidden(A_269,k9_relat_1(C_268,B_270))
      | ~ v1_relat_1(C_268) ) ),
    inference(resolution,[status(thm)],[c_5879,c_2])).

tff(c_6231,plain,
    ( ~ v1_xboole_0('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3185,c_6202])).

tff(c_6287,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_6231])).

tff(c_209868,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209845,c_6287])).

tff(c_209897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199102,c_209868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:13:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 41.65/31.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.77/31.39  
% 41.77/31.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.77/31.39  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k3_tarski > k2_mcart_1 > k1_zfmisc_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 41.77/31.39  
% 41.77/31.39  %Foreground sorts:
% 41.77/31.39  
% 41.77/31.39  
% 41.77/31.39  %Background operators:
% 41.77/31.39  
% 41.77/31.39  
% 41.77/31.39  %Foreground operators:
% 41.77/31.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 41.77/31.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 41.77/31.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 41.77/31.39  tff('#skF_11', type, '#skF_11': $i).
% 41.77/31.39  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 41.77/31.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 41.77/31.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 41.77/31.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 41.77/31.39  tff('#skF_7', type, '#skF_7': $i).
% 41.77/31.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 41.77/31.39  tff('#skF_10', type, '#skF_10': $i).
% 41.77/31.39  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 41.77/31.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 41.77/31.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 41.77/31.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 41.77/31.39  tff('#skF_9', type, '#skF_9': $i).
% 41.77/31.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 41.77/31.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 41.77/31.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 41.77/31.39  tff('#skF_8', type, '#skF_8': $i).
% 41.77/31.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 41.77/31.39  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 41.77/31.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 41.77/31.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 41.77/31.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 41.77/31.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 41.77/31.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 41.77/31.39  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 41.77/31.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 41.77/31.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 41.77/31.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 41.77/31.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 41.77/31.39  
% 41.77/31.41  tff(f_145, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 41.77/31.41  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 41.77/31.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 41.77/31.41  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 41.77/31.41  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 41.77/31.41  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 41.77/31.41  tff(f_90, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 41.77/31.41  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 41.77/31.41  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 41.77/31.41  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 41.77/31.41  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 41.77/31.41  tff(f_108, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 41.77/31.41  tff(f_50, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 41.77/31.41  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 41.77/31.41  tff(c_78, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 41.77/31.41  tff(c_3089, plain, (![A_203, B_204, C_205, D_206]: (k7_relset_1(A_203, B_204, C_205, D_206)=k9_relat_1(C_205, D_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 41.77/31.41  tff(c_3115, plain, (![D_206]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_206)=k9_relat_1('#skF_10', D_206))), inference(resolution, [status(thm)], [c_78, c_3089])).
% 41.77/31.41  tff(c_76, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 41.77/31.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.77/31.41  tff(c_127, plain, (~v1_xboole_0(k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_76, c_2])).
% 41.77/31.41  tff(c_3184, plain, (~v1_xboole_0(k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3115, c_127])).
% 41.77/31.41  tff(c_32, plain, (![A_28, B_29]: (m1_subset_1(A_28, B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 41.77/31.41  tff(c_126, plain, (m1_subset_1('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_76, c_32])).
% 41.77/31.41  tff(c_3183, plain, (m1_subset_1('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3115, c_126])).
% 41.77/31.41  tff(c_128, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 41.77/31.41  tff(c_139, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_128])).
% 41.77/31.41  tff(c_82, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_145])).
% 41.77/31.41  tff(c_3185, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3115, c_76])).
% 41.77/31.41  tff(c_5879, plain, (![A_259, B_260, C_261]: (r2_hidden(k4_tarski('#skF_6'(A_259, B_260, C_261), A_259), C_261) | ~r2_hidden(A_259, k9_relat_1(C_261, B_260)) | ~v1_relat_1(C_261))), inference(cnfTransformation, [status(thm)], [f_80])).
% 41.77/31.41  tff(c_48, plain, (![C_41, A_39, B_40]: (k1_funct_1(C_41, A_39)=B_40 | ~r2_hidden(k4_tarski(A_39, B_40), C_41) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_90])).
% 41.77/31.41  tff(c_39481, plain, (![C_715, A_716, B_717]: (k1_funct_1(C_715, '#skF_6'(A_716, B_717, C_715))=A_716 | ~v1_funct_1(C_715) | ~r2_hidden(A_716, k9_relat_1(C_715, B_717)) | ~v1_relat_1(C_715))), inference(resolution, [status(thm)], [c_5879, c_48])).
% 41.77/31.41  tff(c_39546, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))='#skF_11' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_3185, c_39481])).
% 41.77/31.41  tff(c_39600, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_82, c_39546])).
% 41.77/31.41  tff(c_80, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_145])).
% 41.77/31.41  tff(c_808, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 41.77/31.41  tff(c_824, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_78, c_808])).
% 41.77/31.41  tff(c_7571, plain, (![B_292, A_293, C_294]: (k1_xboole_0=B_292 | k1_relset_1(A_293, B_292, C_294)=A_293 | ~v1_funct_2(C_294, A_293, B_292) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_293, B_292))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 41.77/31.41  tff(c_7594, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_78, c_7571])).
% 41.77/31.41  tff(c_7605, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_824, c_7594])).
% 41.77/31.41  tff(c_7606, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_7605])).
% 41.77/31.41  tff(c_2666, plain, (![A_190, B_191, C_192]: (r2_hidden('#skF_6'(A_190, B_191, C_192), k1_relat_1(C_192)) | ~r2_hidden(A_190, k9_relat_1(C_192, B_191)) | ~v1_relat_1(C_192))), inference(cnfTransformation, [status(thm)], [f_80])).
% 41.77/31.41  tff(c_24170, plain, (![A_531, B_532, C_533]: (m1_subset_1('#skF_6'(A_531, B_532, C_533), k1_relat_1(C_533)) | ~r2_hidden(A_531, k9_relat_1(C_533, B_532)) | ~v1_relat_1(C_533))), inference(resolution, [status(thm)], [c_2666, c_32])).
% 41.77/31.41  tff(c_24173, plain, (![A_531, B_532]: (m1_subset_1('#skF_6'(A_531, B_532, '#skF_10'), '#skF_7') | ~r2_hidden(A_531, k9_relat_1('#skF_10', B_532)) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_7606, c_24170])).
% 41.77/31.41  tff(c_198762, plain, (![A_1573, B_1574]: (m1_subset_1('#skF_6'(A_1573, B_1574, '#skF_10'), '#skF_7') | ~r2_hidden(A_1573, k9_relat_1('#skF_10', B_1574)))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_24173])).
% 41.77/31.41  tff(c_199013, plain, (m1_subset_1('#skF_6'('#skF_11', '#skF_9', '#skF_10'), '#skF_7')), inference(resolution, [status(thm)], [c_3185, c_198762])).
% 41.77/31.41  tff(c_34, plain, (![A_30, B_31]: (r2_hidden(A_30, B_31) | v1_xboole_0(B_31) | ~m1_subset_1(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 41.77/31.41  tff(c_2519, plain, (![A_187, B_188, C_189]: (r2_hidden('#skF_6'(A_187, B_188, C_189), B_188) | ~r2_hidden(A_187, k9_relat_1(C_189, B_188)) | ~v1_relat_1(C_189))), inference(cnfTransformation, [status(thm)], [f_80])).
% 41.77/31.41  tff(c_74, plain, (![F_62]: (k1_funct_1('#skF_10', F_62)!='#skF_11' | ~r2_hidden(F_62, '#skF_9') | ~m1_subset_1(F_62, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 41.77/31.41  tff(c_2833, plain, (![A_195, C_196]: (k1_funct_1('#skF_10', '#skF_6'(A_195, '#skF_9', C_196))!='#skF_11' | ~m1_subset_1('#skF_6'(A_195, '#skF_9', C_196), '#skF_7') | ~r2_hidden(A_195, k9_relat_1(C_196, '#skF_9')) | ~v1_relat_1(C_196))), inference(resolution, [status(thm)], [c_2519, c_74])).
% 41.77/31.41  tff(c_2887, plain, (![A_30, C_196]: (k1_funct_1('#skF_10', '#skF_6'(A_30, '#skF_9', C_196))!='#skF_11' | ~m1_subset_1('#skF_6'(A_30, '#skF_9', C_196), '#skF_7') | ~v1_relat_1(C_196) | v1_xboole_0(k9_relat_1(C_196, '#skF_9')) | ~m1_subset_1(A_30, k9_relat_1(C_196, '#skF_9')))), inference(resolution, [status(thm)], [c_34, c_2833])).
% 41.77/31.41  tff(c_199027, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11' | ~v1_relat_1('#skF_10') | v1_xboole_0(k9_relat_1('#skF_10', '#skF_9')) | ~m1_subset_1('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_199013, c_2887])).
% 41.77/31.41  tff(c_199033, plain, (v1_xboole_0(k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3183, c_139, c_39600, c_199027])).
% 41.77/31.41  tff(c_199035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3184, c_199033])).
% 41.77/31.41  tff(c_199036, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_7605])).
% 41.77/31.41  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 41.77/31.41  tff(c_199102, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_199036, c_6])).
% 41.77/31.41  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.77/31.41  tff(c_161, plain, (![A_83, C_84, B_85]: (r2_hidden(k2_mcart_1(A_83), C_84) | ~r2_hidden(A_83, k2_zfmisc_1(B_85, C_84)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 41.77/31.41  tff(c_201221, plain, (![B_1627, C_1628]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1627, C_1628))), C_1628) | v1_xboole_0(k2_zfmisc_1(B_1627, C_1628)))), inference(resolution, [status(thm)], [c_4, c_161])).
% 41.77/31.41  tff(c_317, plain, (![A_106, C_107]: (r2_hidden('#skF_5'(A_106, k3_tarski(A_106), C_107), A_106) | ~r2_hidden(C_107, k3_tarski(A_106)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 41.77/31.41  tff(c_356, plain, (![A_108, C_109]: (~v1_xboole_0(A_108) | ~r2_hidden(C_109, k3_tarski(A_108)))), inference(resolution, [status(thm)], [c_317, c_2])).
% 41.77/31.41  tff(c_383, plain, (![A_110]: (~v1_xboole_0(A_110) | v1_xboole_0(k3_tarski(A_110)))), inference(resolution, [status(thm)], [c_4, c_356])).
% 41.77/31.41  tff(c_109, plain, (![B_71, A_72]: (~v1_xboole_0(B_71) | B_71=A_72 | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_40])).
% 41.77/31.41  tff(c_112, plain, (![A_72]: (k1_xboole_0=A_72 | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_6, c_109])).
% 41.77/31.41  tff(c_402, plain, (![A_111]: (k3_tarski(A_111)=k1_xboole_0 | ~v1_xboole_0(A_111))), inference(resolution, [status(thm)], [c_383, c_112])).
% 41.77/31.41  tff(c_414, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_402])).
% 41.77/31.41  tff(c_354, plain, (![A_106, C_107]: (~v1_xboole_0(A_106) | ~r2_hidden(C_107, k3_tarski(A_106)))), inference(resolution, [status(thm)], [c_317, c_2])).
% 41.77/31.41  tff(c_422, plain, (![C_107]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_107, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_414, c_354])).
% 41.77/31.41  tff(c_440, plain, (![C_107]: (~r2_hidden(C_107, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_422])).
% 41.77/31.41  tff(c_199095, plain, (![C_107]: (~r2_hidden(C_107, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_199036, c_440])).
% 41.77/31.41  tff(c_201321, plain, (![B_1629]: (v1_xboole_0(k2_zfmisc_1(B_1629, '#skF_8')))), inference(resolution, [status(thm)], [c_201221, c_199095])).
% 41.77/31.41  tff(c_199100, plain, (![A_72]: (A_72='#skF_8' | ~v1_xboole_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_199036, c_112])).
% 41.77/31.41  tff(c_201356, plain, (![B_1629]: (k2_zfmisc_1(B_1629, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_201321, c_199100])).
% 41.77/31.41  tff(c_201369, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_201356, c_78])).
% 41.77/31.41  tff(c_64, plain, (![C_57, A_55]: (k1_xboole_0=C_57 | ~v1_funct_2(C_57, A_55, k1_xboole_0) | k1_xboole_0=A_55 | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 41.77/31.41  tff(c_199072, plain, (![C_57, A_55]: (C_57='#skF_8' | ~v1_funct_2(C_57, A_55, '#skF_8') | A_55='#skF_8' | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_199036, c_199036, c_199036, c_199036, c_64])).
% 41.77/31.41  tff(c_207394, plain, (![C_1742, A_1743]: (C_1742='#skF_8' | ~v1_funct_2(C_1742, A_1743, '#skF_8') | A_1743='#skF_8' | ~m1_subset_1(C_1742, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_201356, c_199072])).
% 41.77/31.41  tff(c_207398, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_8' | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_80, c_207394])).
% 41.77/31.41  tff(c_207405, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_201369, c_207398])).
% 41.77/31.41  tff(c_207406, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_207405])).
% 41.77/31.41  tff(c_199037, plain, (k1_relat_1('#skF_10')!='#skF_7'), inference(splitRight, [status(thm)], [c_7605])).
% 41.77/31.41  tff(c_207420, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_207406, c_199037])).
% 41.77/31.41  tff(c_207430, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_207406, c_824])).
% 41.77/31.41  tff(c_207433, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_207406, c_80])).
% 41.77/31.41  tff(c_170, plain, (![A_86, B_87, C_88]: (r2_hidden(k1_mcart_1(A_86), B_87) | ~r2_hidden(A_86, k2_zfmisc_1(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 41.77/31.41  tff(c_200953, plain, (![B_1616, C_1617]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1616, C_1617))), B_1616) | v1_xboole_0(k2_zfmisc_1(B_1616, C_1617)))), inference(resolution, [status(thm)], [c_4, c_170])).
% 41.77/31.41  tff(c_201049, plain, (![C_1618]: (v1_xboole_0(k2_zfmisc_1('#skF_8', C_1618)))), inference(resolution, [status(thm)], [c_200953, c_199095])).
% 41.77/31.41  tff(c_201078, plain, (![C_1618]: (k2_zfmisc_1('#skF_8', C_1618)='#skF_8')), inference(resolution, [status(thm)], [c_201049, c_199100])).
% 41.77/31.41  tff(c_70, plain, (![B_56, C_57]: (k1_relset_1(k1_xboole_0, B_56, C_57)=k1_xboole_0 | ~v1_funct_2(C_57, k1_xboole_0, B_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_56))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 41.77/31.41  tff(c_199067, plain, (![B_56, C_57]: (k1_relset_1('#skF_8', B_56, C_57)='#skF_8' | ~v1_funct_2(C_57, '#skF_8', B_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_56))))), inference(demodulation, [status(thm), theory('equality')], [c_199036, c_199036, c_199036, c_199036, c_70])).
% 41.77/31.41  tff(c_209834, plain, (![B_1795, C_1796]: (k1_relset_1('#skF_8', B_1795, C_1796)='#skF_8' | ~v1_funct_2(C_1796, '#skF_8', B_1795) | ~m1_subset_1(C_1796, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_201078, c_199067])).
% 41.77/31.41  tff(c_209836, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8' | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_207433, c_209834])).
% 41.77/31.41  tff(c_209842, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_201369, c_207430, c_209836])).
% 41.77/31.41  tff(c_209844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207420, c_209842])).
% 41.77/31.41  tff(c_209845, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_207405])).
% 41.77/31.41  tff(c_6202, plain, (![C_268, A_269, B_270]: (~v1_xboole_0(C_268) | ~r2_hidden(A_269, k9_relat_1(C_268, B_270)) | ~v1_relat_1(C_268))), inference(resolution, [status(thm)], [c_5879, c_2])).
% 41.77/31.41  tff(c_6231, plain, (~v1_xboole_0('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_3185, c_6202])).
% 41.77/31.41  tff(c_6287, plain, (~v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_6231])).
% 41.77/31.41  tff(c_209868, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_209845, c_6287])).
% 41.77/31.41  tff(c_209897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199102, c_209868])).
% 41.77/31.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.77/31.41  
% 41.77/31.41  Inference rules
% 41.77/31.41  ----------------------
% 41.77/31.41  #Ref     : 0
% 41.77/31.41  #Sup     : 54211
% 41.77/31.41  #Fact    : 0
% 41.77/31.41  #Define  : 0
% 41.77/31.41  #Split   : 25
% 41.77/31.41  #Chain   : 0
% 41.77/31.41  #Close   : 0
% 41.77/31.41  
% 41.77/31.41  Ordering : KBO
% 41.77/31.41  
% 41.77/31.41  Simplification rules
% 41.77/31.41  ----------------------
% 41.77/31.41  #Subsume      : 8891
% 41.77/31.41  #Demod        : 73746
% 41.77/31.41  #Tautology    : 31569
% 41.77/31.41  #SimpNegUnit  : 929
% 41.77/31.42  #BackRed      : 155
% 41.77/31.42  
% 41.77/31.42  #Partial instantiations: 0
% 41.77/31.42  #Strategies tried      : 1
% 41.77/31.42  
% 41.77/31.42  Timing (in seconds)
% 41.77/31.42  ----------------------
% 41.77/31.42  Preprocessing        : 0.37
% 41.77/31.42  Parsing              : 0.19
% 41.77/31.42  CNF conversion       : 0.03
% 41.77/31.42  Main loop            : 30.22
% 41.77/31.42  Inferencing          : 3.48
% 41.77/31.42  Reduction            : 6.99
% 41.77/31.42  Demodulation         : 4.98
% 41.77/31.42  BG Simplification    : 0.42
% 41.77/31.42  Subsumption          : 18.17
% 41.77/31.42  Abstraction          : 0.71
% 41.77/31.42  MUC search           : 0.00
% 41.77/31.42  Cooper               : 0.00
% 41.77/31.42  Total                : 30.63
% 41.77/31.42  Index Insertion      : 0.00
% 41.77/31.42  Index Deletion       : 0.00
% 41.77/31.42  Index Matching       : 0.00
% 41.77/31.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
