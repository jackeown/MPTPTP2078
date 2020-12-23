%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1047+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:19 EST 2020

% Result     : Theorem 40.83s
% Output     : CNFRefutation 41.14s
% Verified   : 
% Statistics : Number of formulae       :  313 (106688 expanded)
%              Number of leaves         :   36 (37481 expanded)
%              Depth                    :   44
%              Number of atoms          :  922 (425511 expanded)
%              Number of equality atoms :  220 (66128 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_6 > #skF_7 > #skF_10 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,k1_tarski(B))
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
           => k5_partfun1(A,k1_tarski(B),C) = k1_tarski(D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
         => r1_partfun1(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

tff(f_69,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( r2_hidden(D,k5_partfun1(A,B,C))
         => ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,k1_tarski(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,k1_tarski(B))
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
         => r2_relset_1(A,k1_tarski(B),C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_74,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') != k1_tarski('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_84,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_82,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_80,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_76,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_241,plain,(
    ! [C_123,D_124,A_125,B_126] :
      ( r1_partfun1(C_123,D_124)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_125,k1_tarski(B_126))))
      | ~ v1_funct_1(D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_125,k1_tarski(B_126))))
      | ~ v1_funct_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_248,plain,(
    ! [C_123] :
      ( r1_partfun1(C_123,'#skF_10')
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_123) ) ),
    inference(resolution,[status(thm)],[c_76,c_241])).

tff(c_296,plain,(
    ! [C_133] :
      ( r1_partfun1(C_133,'#skF_10')
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_248])).

tff(c_303,plain,
    ( r1_partfun1('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_296])).

tff(c_310,plain,(
    r1_partfun1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_303])).

tff(c_54,plain,(
    ! [A_52] : ~ v1_xboole_0(k1_tarski(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_174,plain,(
    ! [C_105,A_106,B_107] :
      ( v1_partfun1(C_105,A_106)
      | ~ v1_funct_2(C_105,A_106,B_107)
      | ~ v1_funct_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | v1_xboole_0(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_184,plain,
    ( v1_partfun1('#skF_10','#skF_7')
    | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_10')
    | v1_xboole_0(k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_174])).

tff(c_192,plain,
    ( v1_partfun1('#skF_10','#skF_7')
    | v1_xboole_0(k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_184])).

tff(c_193,plain,(
    v1_partfun1('#skF_10','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_192])).

tff(c_810,plain,(
    ! [F_226,A_227,B_228,C_229] :
      ( r2_hidden(F_226,k5_partfun1(A_227,B_228,C_229))
      | ~ r1_partfun1(C_229,F_226)
      | ~ v1_partfun1(F_226,A_227)
      | ~ m1_subset_1(F_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | ~ v1_funct_1(F_226)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | ~ v1_funct_1(C_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_819,plain,(
    ! [C_229] :
      ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_229))
      | ~ r1_partfun1(C_229,'#skF_10')
      | ~ v1_partfun1('#skF_10','#skF_7')
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_229) ) ),
    inference(resolution,[status(thm)],[c_76,c_810])).

tff(c_828,plain,(
    ! [C_230] :
      ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),C_230))
      | ~ r1_partfun1(C_230,'#skF_10')
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1(C_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_193,c_819])).

tff(c_839,plain,
    ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | ~ r1_partfun1('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_828])).

tff(c_847,plain,(
    r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_310,c_839])).

tff(c_306,plain,
    ( r1_partfun1('#skF_10','#skF_10')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_296])).

tff(c_313,plain,(
    r1_partfun1('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_306])).

tff(c_842,plain,
    ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ r1_partfun1('#skF_10','#skF_10')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_828])).

tff(c_850,plain,(
    r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_313,c_842])).

tff(c_68,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_101,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_82,c_68])).

tff(c_70,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(A_67,k1_zfmisc_1(B_68))
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_399,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( v1_funct_1('#skF_4'(A_163,B_164,C_165,D_166))
      | r2_hidden('#skF_5'(A_163,B_164,C_165,D_166),D_166)
      | k5_partfun1(A_163,B_164,C_165) = D_166
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_407,plain,(
    ! [A_163,B_164,A_67,D_166] :
      ( v1_funct_1('#skF_4'(A_163,B_164,A_67,D_166))
      | r2_hidden('#skF_5'(A_163,B_164,A_67,D_166),D_166)
      | k5_partfun1(A_163,B_164,A_67) = D_166
      | ~ v1_funct_1(A_67)
      | ~ r1_tarski(A_67,k2_zfmisc_1(A_163,B_164)) ) ),
    inference(resolution,[status(thm)],[c_70,c_399])).

tff(c_404,plain,(
    ! [D_166] :
      ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_166))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_166),D_166)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_166
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_82,c_399])).

tff(c_414,plain,(
    ! [D_167] :
      ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_167))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_167),D_167)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_167 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_404])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12,E_48] :
      ( '#skF_6'(k5_partfun1(A_10,B_11,C_12),E_48,B_11,A_10,C_12) = E_48
      | ~ r2_hidden(E_48,k5_partfun1(A_10,B_11,C_12))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_9831,plain,(
    ! [A_1114,B_1115,C_1116] :
      ( '#skF_6'(k5_partfun1(A_1114,B_1115,C_1116),'#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1(A_1114,B_1115,C_1116)),B_1115,A_1114,C_1116) = '#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1(A_1114,B_1115,C_1116))
      | ~ m1_subset_1(C_1116,k1_zfmisc_1(k2_zfmisc_1(A_1114,B_1115)))
      | ~ v1_funct_1(C_1116)
      | v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1(A_1114,B_1115,C_1116)))
      | k5_partfun1(A_1114,B_1115,C_1116) = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_414,c_24])).

tff(c_368,plain,(
    ! [A_141,B_142,C_143,E_144] :
      ( v1_funct_1('#skF_6'(k5_partfun1(A_141,B_142,C_143),E_144,B_142,A_141,C_143))
      | ~ r2_hidden(E_144,k5_partfun1(A_141,B_142,C_143))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_375,plain,(
    ! [E_144] :
      ( v1_funct_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),E_144,k1_tarski('#skF_8'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_144,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_76,c_368])).

tff(c_382,plain,(
    ! [E_144] :
      ( v1_funct_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),E_144,k1_tarski('#skF_8'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_144,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_375])).

tff(c_9959,plain,
    ( v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10')
    | v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_9831,c_382])).

tff(c_9998,plain,
    ( v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_9959])).

tff(c_10012,plain,(
    ~ r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_9998])).

tff(c_10084,plain,
    ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ r1_tarski('#skF_9',k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_407,c_10012])).

tff(c_10142,plain,
    ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_84,c_10084])).

tff(c_10145,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_10142])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( '#skF_1'(A_5,B_6) = A_5
      | r2_hidden('#skF_2'(A_5,B_6),B_6)
      | k1_tarski(A_5) = B_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_194,plain,(
    ! [D_108,A_109,B_110,C_111] :
      ( v1_funct_2(D_108,A_109,B_110)
      | ~ r2_hidden(D_108,k5_partfun1(A_109,B_110,C_111))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_202,plain,(
    ! [A_5,A_109,B_110,C_111] :
      ( v1_funct_2('#skF_2'(A_5,k5_partfun1(A_109,B_110,C_111)),A_109,B_110)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(C_111)
      | '#skF_1'(A_5,k5_partfun1(A_109,B_110,C_111)) = A_5
      | k5_partfun1(A_109,B_110,C_111) = k1_tarski(A_5) ) ),
    inference(resolution,[status(thm)],[c_16,c_194])).

tff(c_10643,plain,(
    ! [A_5] :
      ( v1_funct_2('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | '#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = A_5
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10145,c_202])).

tff(c_10962,plain,(
    ! [A_5] :
      ( v1_funct_2('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_5
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10145,c_10145,c_80,c_76,c_10643])).

tff(c_232,plain,(
    ! [D_119,A_120,B_121,C_122] :
      ( m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ r2_hidden(D_119,k5_partfun1(A_120,B_121,C_122))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_240,plain,(
    ! [A_5,A_120,B_121,C_122] :
      ( m1_subset_1('#skF_2'(A_5,k5_partfun1(A_120,B_121,C_122)),k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(C_122)
      | '#skF_1'(A_5,k5_partfun1(A_120,B_121,C_122)) = A_5
      | k5_partfun1(A_120,B_121,C_122) = k1_tarski(A_5) ) ),
    inference(resolution,[status(thm)],[c_16,c_232])).

tff(c_10631,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | '#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = A_5
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10145,c_240])).

tff(c_10954,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | '#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_5
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10145,c_10145,c_80,c_76,c_10631])).

tff(c_10225,plain,(
    ! [E_144] :
      ( v1_funct_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_144,k1_tarski('#skF_8'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_144,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10145,c_10145,c_382])).

tff(c_10672,plain,(
    ! [E_48] :
      ( '#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),E_48,k1_tarski('#skF_8'),'#skF_7','#skF_10') = E_48
      | ~ r2_hidden(E_48,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10145,c_24])).

tff(c_10982,plain,(
    ! [E_48] :
      ( '#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_48,k1_tarski('#skF_8'),'#skF_7','#skF_10') = E_48
      | ~ r2_hidden(E_48,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_10145,c_10672])).

tff(c_26,plain,(
    ! [A_10,B_11,C_12,E_48] :
      ( m1_subset_1('#skF_6'(k5_partfun1(A_10,B_11,C_12),E_48,B_11,A_10,C_12),k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ r2_hidden(E_48,k5_partfun1(A_10,B_11,C_12))
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10661,plain,(
    ! [E_48] :
      ( m1_subset_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_48,k1_tarski('#skF_8'),'#skF_7','#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(E_48,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10145,c_26])).

tff(c_16556,plain,(
    ! [E_1177] :
      ( m1_subset_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_1177,k1_tarski('#skF_8'),'#skF_7','#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(E_1177,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_10145,c_10661])).

tff(c_1396,plain,(
    ! [A_263,B_264,C_265,D_266] :
      ( r2_relset_1(A_263,k1_tarski(B_264),C_265,D_266)
      | ~ m1_subset_1(D_266,k1_zfmisc_1(k2_zfmisc_1(A_263,k1_tarski(B_264))))
      | ~ v1_funct_2(D_266,A_263,k1_tarski(B_264))
      | ~ v1_funct_1(D_266)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,k1_tarski(B_264))))
      | ~ v1_funct_2(C_265,A_263,k1_tarski(B_264))
      | ~ v1_funct_1(C_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1409,plain,(
    ! [C_265] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),C_265,'#skF_10')
      | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2(C_265,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1(C_265) ) ),
    inference(resolution,[status(thm)],[c_76,c_1396])).

tff(c_1418,plain,(
    ! [C_265] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),C_265,'#skF_10')
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2(C_265,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1(C_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1409])).

tff(c_29410,plain,(
    ! [E_1614] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_1614,k1_tarski('#skF_8'),'#skF_7','#skF_10'),'#skF_10')
      | ~ v1_funct_2('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_1614,k1_tarski('#skF_8'),'#skF_7','#skF_10'),'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_1614,k1_tarski('#skF_8'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_1614,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_16556,c_1418])).

tff(c_38947,plain,(
    ! [E_1926] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_1926,'#skF_10')
      | ~ v1_funct_2('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_1926,k1_tarski('#skF_8'),'#skF_7','#skF_10'),'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_1926,k1_tarski('#skF_8'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_1926,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_1926,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10982,c_29410])).

tff(c_38965,plain,(
    ! [E_1927] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_1927,'#skF_10')
      | ~ v1_funct_2(E_1927,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_1927,k1_tarski('#skF_8'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_1927,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_1927,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_1927,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10982,c_38947])).

tff(c_38987,plain,(
    ! [E_1928] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_1928,'#skF_10')
      | ~ v1_funct_2(E_1928,'#skF_7',k1_tarski('#skF_8'))
      | ~ r2_hidden(E_1928,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_10225,c_38965])).

tff(c_39574,plain,(
    ! [A_1934] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_2'(A_1934,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_10')
      | ~ v1_funct_2('#skF_2'(A_1934,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_1934,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1934
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1934) ) ),
    inference(resolution,[status(thm)],[c_16,c_38987])).

tff(c_58,plain,(
    ! [D_56,C_55,A_53,B_54] :
      ( D_56 = C_55
      | ~ r2_relset_1(A_53,B_54,C_55,D_56)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_39576,plain,(
    ! [A_1934] :
      ( '#skF_2'(A_1934,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ m1_subset_1('#skF_2'(A_1934,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2('#skF_2'(A_1934,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_1934,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1934
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1934) ) ),
    inference(resolution,[status(thm)],[c_39574,c_58])).

tff(c_40451,plain,(
    ! [A_1967] :
      ( '#skF_2'(A_1967,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ m1_subset_1('#skF_2'(A_1967,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2('#skF_2'(A_1967,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_1967,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1967
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1967) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_39576])).

tff(c_40475,plain,(
    ! [A_1968] :
      ( '#skF_2'(A_1968,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ v1_funct_2('#skF_2'(A_1968,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_1968,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1968
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1968) ) ),
    inference(resolution,[status(thm)],[c_10954,c_40451])).

tff(c_40483,plain,(
    ! [A_5] :
      ( '#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_5
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(resolution,[status(thm)],[c_10962,c_40475])).

tff(c_844,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),A_67))
      | ~ r1_partfun1(A_67,'#skF_10')
      | ~ v1_funct_1(A_67)
      | ~ r1_tarski(A_67,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_70,c_828])).

tff(c_40488,plain,(
    ! [A_1969] :
      ( '#skF_2'(A_1969,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_1969,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1969
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1969) ) ),
    inference(resolution,[status(thm)],[c_10962,c_40475])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( '#skF_1'(A_5,B_6) = A_5
      | '#skF_2'(A_5,B_6) != A_5
      | k1_tarski(A_5) = B_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40667,plain,(
    ! [A_1969] :
      ( '#skF_1'(A_1969,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1969
      | A_1969 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1969)
      | '#skF_1'(A_1969,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1969
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1969) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40488,c_12])).

tff(c_40828,plain,(
    ! [A_1973] :
      ( A_1973 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1973)
      | '#skF_1'(A_1973,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_1973 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_40667])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | '#skF_2'(A_5,B_6) != A_5
      | k1_tarski(A_5) = B_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_41169,plain,(
    ! [A_1983] :
      ( ~ r2_hidden(A_1983,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | '#skF_2'(A_1983,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != A_1983
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1983)
      | A_1983 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_1983) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40828,c_10])).

tff(c_41441,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10')
    | ~ r1_partfun1('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_9')
    | ~ r1_tarski('#skF_9',k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_844,c_41169])).

tff(c_41588,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_84,c_310,c_41441])).

tff(c_41589,plain,(
    '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_41588])).

tff(c_41610,plain,
    ( '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_40483,c_41589])).

tff(c_41613,plain,(
    '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_41610])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r2_hidden('#skF_2'(A_5,B_6),B_6)
      | k1_tarski(A_5) = B_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_239,plain,(
    ! [A_5,A_120,B_121,C_122] :
      ( m1_subset_1('#skF_2'(A_5,k5_partfun1(A_120,B_121,C_122)),k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(C_122)
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1(A_120,B_121,C_122)),k5_partfun1(A_120,B_121,C_122))
      | k5_partfun1(A_120,B_121,C_122) = k1_tarski(A_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_232])).

tff(c_41674,plain,
    ( m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9')
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_41613,c_239])).

tff(c_41757,plain,
    ( m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_84,c_82,c_41674])).

tff(c_41758,plain,(
    m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_41757])).

tff(c_164,plain,(
    ! [D_99,A_100,B_101,C_102] :
      ( v1_funct_1(D_99)
      | ~ r2_hidden(D_99,k5_partfun1(A_100,B_101,C_102))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_171,plain,(
    ! [A_5,A_100,B_101,C_102] :
      ( v1_funct_1('#skF_2'(A_5,k5_partfun1(A_100,B_101,C_102)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_1(C_102)
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1(A_100,B_101,C_102)),k5_partfun1(A_100,B_101,C_102))
      | k5_partfun1(A_100,B_101,C_102) = k1_tarski(A_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_164])).

tff(c_10637,plain,(
    ! [A_5] :
      ( v1_funct_1('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10145,c_171])).

tff(c_10958,plain,(
    ! [A_5] :
      ( v1_funct_1('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10145,c_10145,c_80,c_76,c_10145,c_10637])).

tff(c_41670,plain,
    ( v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_41613,c_10958])).

tff(c_41751,plain,
    ( v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_41670])).

tff(c_41752,plain,(
    v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_41751])).

tff(c_201,plain,(
    ! [A_5,A_109,B_110,C_111] :
      ( v1_funct_2('#skF_2'(A_5,k5_partfun1(A_109,B_110,C_111)),A_109,B_110)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(C_111)
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1(A_109,B_110,C_111)),k5_partfun1(A_109,B_110,C_111))
      | k5_partfun1(A_109,B_110,C_111) = k1_tarski(A_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_194])).

tff(c_41677,plain,
    ( v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9')
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_41613,c_201])).

tff(c_41760,plain,
    ( v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_84,c_82,c_41677])).

tff(c_41761,plain,(
    v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_41760])).

tff(c_62,plain,(
    ! [D_66,A_62,B_63,C_64] :
      ( m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ r2_hidden(D_66,k5_partfun1(A_62,B_63,C_64))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10674,plain,(
    ! [D_66] :
      ( m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(D_66,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10145,c_62])).

tff(c_11592,plain,(
    ! [D_1124] :
      ( m1_subset_1(D_1124,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(D_1124,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_10674])).

tff(c_12193,plain,(
    ! [D_1127] :
      ( r1_tarski(D_1127,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
      | ~ r2_hidden(D_1127,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_11592,c_68])).

tff(c_12442,plain,(
    ! [A_5] :
      ( r1_tarski('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_12193])).

tff(c_41655,plain,
    ( r1_tarski('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_41613,c_12442])).

tff(c_41736,plain,
    ( r1_tarski('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_41655])).

tff(c_41737,plain,(
    r1_tarski('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_41736])).

tff(c_2405,plain,(
    ! [A_378,B_379,C_380,A_381] :
      ( r2_relset_1(A_378,k1_tarski(B_379),C_380,A_381)
      | ~ v1_funct_2(A_381,A_378,k1_tarski(B_379))
      | ~ v1_funct_1(A_381)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_378,k1_tarski(B_379))))
      | ~ v1_funct_2(C_380,A_378,k1_tarski(B_379))
      | ~ v1_funct_1(C_380)
      | ~ r1_tarski(A_381,k2_zfmisc_1(A_378,k1_tarski(B_379))) ) ),
    inference(resolution,[status(thm)],[c_70,c_1396])).

tff(c_2428,plain,(
    ! [A_381] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10',A_381)
      | ~ v1_funct_2(A_381,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1(A_381)
      | ~ v1_funct_2('#skF_10','#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_10')
      | ~ r1_tarski(A_381,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_76,c_2405])).

tff(c_2441,plain,(
    ! [A_381] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10',A_381)
      | ~ v1_funct_2(A_381,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1(A_381)
      | ~ r1_tarski(A_381,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2428])).

tff(c_41997,plain,
    ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10','#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
    | ~ v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(resolution,[status(thm)],[c_41737,c_2441])).

tff(c_42063,plain,(
    r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_10','#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41752,c_41761,c_41997])).

tff(c_42099,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | ~ m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(resolution,[status(thm)],[c_42063,c_58])).

tff(c_42105,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | ~ m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_42099])).

tff(c_42106,plain,(
    ~ m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_41589,c_42105])).

tff(c_42337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41758,c_42106])).

tff(c_42339,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') != k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_10142])).

tff(c_50,plain,(
    ! [A_10,B_11,C_12,D_34] :
      ( m1_subset_1('#skF_4'(A_10,B_11,C_12,D_34),k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | r2_hidden('#skF_5'(A_10,B_11,C_12,D_34),D_34)
      | k5_partfun1(A_10,B_11,C_12) = D_34
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42338,plain,(
    v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_10142])).

tff(c_565,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( v1_partfun1('#skF_4'(A_187,B_188,C_189,D_190),A_187)
      | r2_hidden('#skF_5'(A_187,B_188,C_189,D_190),D_190)
      | k5_partfun1(A_187,B_188,C_189) = D_190
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_570,plain,(
    ! [D_190] :
      ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_190),'#skF_7')
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_190),D_190)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_190
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_82,c_565])).

tff(c_576,plain,(
    ! [D_190] :
      ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_190),'#skF_7')
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_190),D_190)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_190 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_570])).

tff(c_10136,plain,
    ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_576,c_10012])).

tff(c_42350,plain,(
    v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_42339,c_10136])).

tff(c_458,plain,(
    ! [C_169,A_170,B_171,D_172] :
      ( r1_partfun1(C_169,'#skF_4'(A_170,B_171,C_169,D_172))
      | r2_hidden('#skF_5'(A_170,B_171,C_169,D_172),D_172)
      | k5_partfun1(A_170,B_171,C_169) = D_172
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_463,plain,(
    ! [D_172] :
      ( r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_172))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_172),D_172)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_172
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_82,c_458])).

tff(c_469,plain,(
    ! [D_172] :
      ( r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_172))
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_172),D_172)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_172 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_463])).

tff(c_10143,plain,
    ( r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_469,c_10012])).

tff(c_42342,plain,(
    r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42339,c_10143])).

tff(c_925,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( m1_subset_1('#skF_4'(A_231,B_232,C_233,D_234),k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | r2_hidden('#skF_5'(A_231,B_232,C_233,D_234),D_234)
      | k5_partfun1(A_231,B_232,C_233) = D_234
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_993,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( r1_tarski('#skF_4'(A_231,B_232,C_233,D_234),k2_zfmisc_1(A_231,B_232))
      | r2_hidden('#skF_5'(A_231,B_232,C_233,D_234),D_234)
      | k5_partfun1(A_231,B_232,C_233) = D_234
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_1(C_233) ) ),
    inference(resolution,[status(thm)],[c_925,c_68])).

tff(c_10053,plain,
    ( r1_tarski('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_993,c_10012])).

tff(c_10120,plain,
    ( r1_tarski('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_10053])).

tff(c_42353,plain,(
    r1_tarski('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_42339,c_10120])).

tff(c_1050,plain,(
    ! [A_236,A_237,B_238,C_239] :
      ( r2_hidden(A_236,k5_partfun1(A_237,B_238,C_239))
      | ~ r1_partfun1(C_239,A_236)
      | ~ v1_partfun1(A_236,A_237)
      | ~ v1_funct_1(A_236)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ v1_funct_1(C_239)
      | ~ r1_tarski(A_236,k2_zfmisc_1(A_237,B_238)) ) ),
    inference(resolution,[status(thm)],[c_70,c_810])).

tff(c_1059,plain,(
    ! [A_236] :
      ( r2_hidden(A_236,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r1_partfun1('#skF_9',A_236)
      | ~ v1_partfun1(A_236,'#skF_7')
      | ~ v1_funct_1(A_236)
      | ~ v1_funct_1('#skF_9')
      | ~ r1_tarski(A_236,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_82,c_1050])).

tff(c_1071,plain,(
    ! [A_240] :
      ( r2_hidden(A_240,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r1_partfun1('#skF_9',A_240)
      | ~ v1_partfun1(A_240,'#skF_7')
      | ~ v1_funct_1(A_240)
      | ~ r1_tarski(A_240,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1059])).

tff(c_64,plain,(
    ! [D_66,A_62,B_63,C_64] :
      ( v1_funct_2(D_66,A_62,B_63)
      | ~ r2_hidden(D_66,k5_partfun1(A_62,B_63,C_64))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1077,plain,(
    ! [A_240] :
      ( v1_funct_2(A_240,'#skF_7',k1_tarski('#skF_8'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_9')
      | ~ r1_partfun1('#skF_9',A_240)
      | ~ v1_partfun1(A_240,'#skF_7')
      | ~ v1_funct_1(A_240)
      | ~ r1_tarski(A_240,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_1071,c_64])).

tff(c_1092,plain,(
    ! [A_240] :
      ( v1_funct_2(A_240,'#skF_7',k1_tarski('#skF_8'))
      | ~ r1_partfun1('#skF_9',A_240)
      | ~ v1_partfun1(A_240,'#skF_7')
      | ~ v1_funct_1(A_240)
      | ~ r1_tarski(A_240,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_1077])).

tff(c_42379,plain,
    ( v1_funct_2('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
    | ~ r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_42353,c_1092])).

tff(c_42431,plain,(
    v1_funct_2('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42338,c_42350,c_42342,c_42379])).

tff(c_1419,plain,(
    ! [C_267] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),C_267,'#skF_10')
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2(C_267,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1(C_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1409])).

tff(c_1440,plain,(
    ! [A_67] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),A_67,'#skF_10')
      | ~ v1_funct_2(A_67,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1(A_67)
      | ~ r1_tarski(A_67,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_70,c_1419])).

tff(c_42373,plain,
    ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10')
    | ~ v1_funct_2('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_42353,c_1440])).

tff(c_42425,plain,
    ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10')
    | ~ v1_funct_2('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42338,c_42373])).

tff(c_42798,plain,(
    r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42431,c_42425])).

tff(c_42800,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(resolution,[status(thm)],[c_42798,c_58])).

tff(c_42803,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_42800])).

tff(c_42804,plain,(
    ~ m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(splitLeft,[status(thm)],[c_42803])).

tff(c_42822,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_42804])).

tff(c_42848,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_42822])).

tff(c_42850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42339,c_10012,c_42848])).

tff(c_42851,plain,(
    '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_42803])).

tff(c_1161,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( '#skF_4'(A_244,B_245,C_246,D_247) = '#skF_3'(A_244,B_245,C_246,D_247)
      | r2_hidden('#skF_5'(A_244,B_245,C_246,D_247),D_247)
      | k5_partfun1(A_244,B_245,C_246) = D_247
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ v1_funct_1(C_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1170,plain,(
    ! [D_247] :
      ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_247) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_247)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_247),D_247)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_247
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_82,c_1161])).

tff(c_1178,plain,(
    ! [D_247] :
      ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_247) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_247)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_247),D_247)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_247 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1170])).

tff(c_10127,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1178,c_10012])).

tff(c_42853,plain,(
    '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_42339,c_10127])).

tff(c_43099,plain,(
    '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42851,c_42853])).

tff(c_580,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( ~ r2_hidden('#skF_3'(A_191,B_192,C_193,D_194),D_194)
      | r2_hidden('#skF_5'(A_191,B_192,C_193,D_194),D_194)
      | k5_partfun1(A_191,B_192,C_193) = D_194
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192)))
      | ~ v1_funct_1(C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_585,plain,(
    ! [D_194] :
      ( ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_194),D_194)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_194),D_194)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_194
      | ~ v1_funct_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_82,c_580])).

tff(c_591,plain,(
    ! [D_194] :
      ( ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_194),D_194)
      | r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',D_194),D_194)
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = D_194 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_585])).

tff(c_10135,plain,
    ( ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_591,c_10012])).

tff(c_42587,plain,(
    ~ r2_hidden('#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_42339,c_10135])).

tff(c_43335,plain,(
    ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43099,c_42587])).

tff(c_43339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_43335])).

tff(c_43341,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_9998])).

tff(c_43345,plain,
    ( m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_43341,c_62])).

tff(c_43355,plain,(
    m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_43345])).

tff(c_66,plain,(
    ! [D_66,A_62,B_63,C_64] :
      ( v1_funct_1(D_66)
      | ~ r2_hidden(D_66,k5_partfun1(A_62,B_63,C_64))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_43349,plain,
    ( v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_43341,c_66])).

tff(c_43361,plain,(
    v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_43349])).

tff(c_43347,plain,
    ( v1_funct_2('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_43341,c_64])).

tff(c_43358,plain,(
    v1_funct_2('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_43347])).

tff(c_43497,plain,
    ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10')
    | ~ v1_funct_2('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_43355,c_1418])).

tff(c_43571,plain,(
    r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43361,c_43358,c_43497])).

tff(c_44059,plain,
    ( '#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(resolution,[status(thm)],[c_43571,c_58])).

tff(c_44062,plain,(
    '#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43355,c_76,c_44059])).

tff(c_40,plain,(
    ! [A_10,B_11,C_12,D_34] :
      ( v1_funct_1('#skF_4'(A_10,B_11,C_12,D_34))
      | ~ r1_partfun1(C_12,'#skF_5'(A_10,B_11,C_12,D_34))
      | ~ v1_partfun1('#skF_5'(A_10,B_11,C_12,D_34),A_10)
      | ~ m1_subset_1('#skF_5'(A_10,B_11,C_12,D_34),k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1('#skF_5'(A_10,B_11,C_12,D_34))
      | k5_partfun1(A_10,B_11,C_12) = D_34
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44294,plain,
    ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r1_partfun1('#skF_9','#skF_10')
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_44062,c_40])).

tff(c_44457,plain,
    ( v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_44062,c_76,c_44062,c_193,c_44062,c_310,c_44294])).

tff(c_44588,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_44457])).

tff(c_45107,plain,(
    ! [A_5] :
      ( v1_funct_2('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | '#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = A_5
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44588,c_202])).

tff(c_45428,plain,(
    ! [A_5] :
      ( v1_funct_2('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_5
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44588,c_44588,c_80,c_76,c_45107])).

tff(c_45095,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | '#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = A_5
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44588,c_240])).

tff(c_45420,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | '#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_5
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44588,c_44588,c_80,c_76,c_45095])).

tff(c_44686,plain,(
    ! [E_144] :
      ( v1_funct_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_144,k1_tarski('#skF_8'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_144,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44588,c_44588,c_382])).

tff(c_45136,plain,(
    ! [E_48] :
      ( '#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'),E_48,k1_tarski('#skF_8'),'#skF_7','#skF_10') = E_48
      | ~ r2_hidden(E_48,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44588,c_24])).

tff(c_45448,plain,(
    ! [E_48] :
      ( '#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_48,k1_tarski('#skF_8'),'#skF_7','#skF_10') = E_48
      | ~ r2_hidden(E_48,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_44588,c_45136])).

tff(c_45125,plain,(
    ! [E_48] :
      ( m1_subset_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_48,k1_tarski('#skF_8'),'#skF_7','#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(E_48,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44588,c_26])).

tff(c_51292,plain,(
    ! [E_2077] :
      ( m1_subset_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_2077,k1_tarski('#skF_8'),'#skF_7','#skF_10'),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(E_2077,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_44588,c_45125])).

tff(c_64406,plain,(
    ! [E_2512] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_2512,k1_tarski('#skF_8'),'#skF_7','#skF_10'),'#skF_10')
      | ~ v1_funct_2('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_2512,k1_tarski('#skF_8'),'#skF_7','#skF_10'),'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_2512,k1_tarski('#skF_8'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_2512,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_51292,c_1418])).

tff(c_74663,plain,(
    ! [E_2838] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_2838,'#skF_10')
      | ~ v1_funct_2('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_2838,k1_tarski('#skF_8'),'#skF_7','#skF_10'),'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_2838,k1_tarski('#skF_8'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_2838,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_2838,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45448,c_64406])).

tff(c_74687,plain,(
    ! [E_2844] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_2844,'#skF_10')
      | ~ v1_funct_2(E_2844,'#skF_7',k1_tarski('#skF_8'))
      | ~ v1_funct_1('#skF_6'(k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'),E_2844,k1_tarski('#skF_8'),'#skF_7','#skF_10'))
      | ~ r2_hidden(E_2844,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_2844,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ r2_hidden(E_2844,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45448,c_74663])).

tff(c_74709,plain,(
    ! [E_2845] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),E_2845,'#skF_10')
      | ~ v1_funct_2(E_2845,'#skF_7',k1_tarski('#skF_8'))
      | ~ r2_hidden(E_2845,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_44686,c_74687])).

tff(c_75163,plain,(
    ! [A_2846] :
      ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_2'(A_2846,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_10')
      | ~ v1_funct_2('#skF_2'(A_2846,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_2846,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2846
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2846) ) ),
    inference(resolution,[status(thm)],[c_16,c_74709])).

tff(c_75165,plain,(
    ! [A_2846] :
      ( '#skF_2'(A_2846,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ m1_subset_1('#skF_2'(A_2846,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2('#skF_2'(A_2846,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_2846,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2846
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2846) ) ),
    inference(resolution,[status(thm)],[c_75163,c_58])).

tff(c_75436,plain,(
    ! [A_2866] :
      ( '#skF_2'(A_2866,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ m1_subset_1('#skF_2'(A_2866,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_2('#skF_2'(A_2866,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_2866,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2866
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2866) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_75165])).

tff(c_75487,plain,(
    ! [A_2873] :
      ( '#skF_2'(A_2873,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | ~ v1_funct_2('#skF_2'(A_2873,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | '#skF_1'(A_2873,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2873
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2873) ) ),
    inference(resolution,[status(thm)],[c_45420,c_75436])).

tff(c_75495,plain,(
    ! [A_5] :
      ( '#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_5
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(resolution,[status(thm)],[c_45428,c_75487])).

tff(c_75500,plain,(
    ! [A_2874] :
      ( '#skF_2'(A_2874,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
      | '#skF_1'(A_2874,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2874
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2874) ) ),
    inference(resolution,[status(thm)],[c_45428,c_75487])).

tff(c_75685,plain,(
    ! [A_2874] :
      ( '#skF_1'(A_2874,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2874
      | A_2874 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2874)
      | '#skF_1'(A_2874,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2874
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2874) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75500,c_12])).

tff(c_75850,plain,(
    ! [A_2878] :
      ( A_2878 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2878)
      | '#skF_1'(A_2878,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = A_2878 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_75685])).

tff(c_76176,plain,(
    ! [A_2891] :
      ( ~ r2_hidden(A_2891,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | '#skF_2'(A_2891,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != A_2891
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2891)
      | A_2891 != '#skF_10'
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_2891) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75850,c_10])).

tff(c_76452,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10')
    | ~ r1_partfun1('#skF_9','#skF_10')
    | ~ v1_funct_1('#skF_9')
    | ~ r1_tarski('#skF_9',k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_844,c_76176])).

tff(c_76615,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_84,c_310,c_76452])).

tff(c_76616,plain,(
    '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_76615])).

tff(c_76649,plain,
    ( '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_75495,c_76616])).

tff(c_76652,plain,(
    '#skF_1'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_76649])).

tff(c_76713,plain,
    ( m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9')
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_76652,c_239])).

tff(c_76796,plain,
    ( m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_84,c_82,c_76713])).

tff(c_76797,plain,(
    m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_76796])).

tff(c_45101,plain,(
    ! [A_5] :
      ( v1_funct_1('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44588,c_171])).

tff(c_45424,plain,(
    ! [A_5] :
      ( v1_funct_1('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44588,c_44588,c_80,c_76,c_44588,c_45101])).

tff(c_76709,plain,
    ( v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_76652,c_45424])).

tff(c_76790,plain,
    ( v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_76709])).

tff(c_76791,plain,(
    v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_76790])).

tff(c_45086,plain,(
    ! [A_5] :
      ( v1_funct_2('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10')
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k1_tarski(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44588,c_201])).

tff(c_45414,plain,(
    ! [A_5] :
      ( v1_funct_2('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44588,c_44588,c_80,c_76,c_44588,c_45086])).

tff(c_76706,plain,
    ( v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_76652,c_45414])).

tff(c_76787,plain,
    ( v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_76706])).

tff(c_76788,plain,(
    v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_76787])).

tff(c_45138,plain,(
    ! [D_66] :
      ( m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(D_66,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44588,c_62])).

tff(c_46441,plain,(
    ! [D_2023] :
      ( m1_subset_1(D_2023,k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
      | ~ r2_hidden(D_2023,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_45138])).

tff(c_47089,plain,(
    ! [D_2032] :
      ( r1_tarski(D_2032,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
      | ~ r2_hidden(D_2032,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_46441,c_68])).

tff(c_47346,plain,(
    ! [A_5] :
      ( r1_tarski('#skF_2'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
      | ~ r2_hidden('#skF_1'(A_5,k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
      | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski(A_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_47089])).

tff(c_76694,plain,
    ( r1_tarski('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_76652,c_47346])).

tff(c_76775,plain,
    ( r1_tarski('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_76694])).

tff(c_76776,plain,(
    r1_tarski('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_76775])).

tff(c_77046,plain,
    ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_10')
    | ~ v1_funct_2('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(resolution,[status(thm)],[c_76776,c_1440])).

tff(c_77113,plain,(
    r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76791,c_76788,c_77046])).

tff(c_77154,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(resolution,[status(thm)],[c_77113,c_58])).

tff(c_77160,plain,
    ( '#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')) = '#skF_10'
    | ~ m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_77154])).

tff(c_77161,plain,(
    ~ m1_subset_1('#skF_2'('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_76616,c_77160])).

tff(c_77354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76797,c_77161])).

tff(c_77356,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') != k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_44457])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( v1_partfun1(C_4,A_1)
      | ~ v1_funct_2(C_4,A_1,B_2)
      | ~ v1_funct_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | v1_xboole_0(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_43533,plain,
    ( v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ v1_funct_2('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | v1_xboole_0(k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_43355,c_2])).

tff(c_43619,plain,
    ( v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | v1_xboole_0(k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43361,c_43358,c_43533])).

tff(c_43620,plain,(
    v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_43619])).

tff(c_43622,plain,(
    r1_tarski('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_43355,c_68])).

tff(c_327,plain,(
    ! [C_135,A_136,A_137,B_138] :
      ( r1_partfun1(C_135,A_136)
      | ~ v1_funct_1(A_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_137,k1_tarski(B_138))))
      | ~ v1_funct_1(C_135)
      | ~ r1_tarski(A_136,k2_zfmisc_1(A_137,k1_tarski(B_138))) ) ),
    inference(resolution,[status(thm)],[c_70,c_241])).

tff(c_332,plain,(
    ! [A_136] :
      ( r1_partfun1('#skF_9',A_136)
      | ~ v1_funct_1(A_136)
      | ~ v1_funct_1('#skF_9')
      | ~ r1_tarski(A_136,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(resolution,[status(thm)],[c_82,c_327])).

tff(c_338,plain,(
    ! [A_136] :
      ( r1_partfun1('#skF_9',A_136)
      | ~ v1_funct_1(A_136)
      | ~ r1_tarski(A_136,k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_332])).

tff(c_43779,plain,
    ( r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_43622,c_338])).

tff(c_43835,plain,(
    r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43361,c_43779])).

tff(c_38,plain,(
    ! [A_10,B_11,C_12,D_34] :
      ( m1_subset_1('#skF_4'(A_10,B_11,C_12,D_34),k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ r1_partfun1(C_12,'#skF_5'(A_10,B_11,C_12,D_34))
      | ~ v1_partfun1('#skF_5'(A_10,B_11,C_12,D_34),A_10)
      | ~ m1_subset_1('#skF_5'(A_10,B_11,C_12,D_34),k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1('#skF_5'(A_10,B_11,C_12,D_34))
      | k5_partfun1(A_10,B_11,C_12) = D_34
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_43855,plain,
    ( m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_43835,c_38])).

tff(c_43867,plain,
    ( m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_43361,c_43355,c_43620,c_43855])).

tff(c_77505,plain,(
    m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(negUnitSimplification,[status(thm)],[c_77356,c_43867])).

tff(c_77355,plain,(
    v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_44457])).

tff(c_34,plain,(
    ! [A_10,B_11,C_12,D_34] :
      ( v1_partfun1('#skF_4'(A_10,B_11,C_12,D_34),A_10)
      | ~ r1_partfun1(C_12,'#skF_5'(A_10,B_11,C_12,D_34))
      | ~ v1_partfun1('#skF_5'(A_10,B_11,C_12,D_34),A_10)
      | ~ m1_subset_1('#skF_5'(A_10,B_11,C_12,D_34),k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1('#skF_5'(A_10,B_11,C_12,D_34))
      | k5_partfun1(A_10,B_11,C_12) = D_34
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_43857,plain,
    ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_43835,c_34])).

tff(c_43870,plain,
    ( v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_43361,c_43355,c_43620,c_43857])).

tff(c_77381,plain,(
    v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_77356,c_43870])).

tff(c_32,plain,(
    ! [C_12,A_10,B_11,D_34] :
      ( r1_partfun1(C_12,'#skF_4'(A_10,B_11,C_12,D_34))
      | ~ r1_partfun1(C_12,'#skF_5'(A_10,B_11,C_12,D_34))
      | ~ v1_partfun1('#skF_5'(A_10,B_11,C_12,D_34),A_10)
      | ~ m1_subset_1('#skF_5'(A_10,B_11,C_12,D_34),k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1('#skF_5'(A_10,B_11,C_12,D_34))
      | k5_partfun1(A_10,B_11,C_12) = D_34
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44286,plain,
    ( r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_44062,c_32])).

tff(c_44451,plain,
    ( r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_44062,c_76,c_193,c_44062,c_310,c_44062,c_44286])).

tff(c_77375,plain,(
    r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_77356,c_44451])).

tff(c_77648,plain,(
    r1_tarski('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_77505,c_68])).

tff(c_77878,plain,
    ( v1_funct_2('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
    | ~ r1_partfun1('#skF_9','#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_partfun1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_77648,c_1092])).

tff(c_77930,plain,(
    v1_funct_2('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77355,c_77381,c_77375,c_77878])).

tff(c_77526,plain,
    ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10')
    | ~ v1_funct_2('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8'))
    | ~ v1_funct_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))) ),
    inference(resolution,[status(thm)],[c_77505,c_1418])).

tff(c_77597,plain,
    ( r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10')
    | ~ v1_funct_2('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77355,c_77526])).

tff(c_78549,plain,(
    r2_relset_1('#skF_7',k1_tarski('#skF_8'),'#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77930,c_77597])).

tff(c_78551,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ m1_subset_1('#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8')))) ),
    inference(resolution,[status(thm)],[c_78549,c_58])).

tff(c_78554,plain,(
    '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77505,c_76,c_78551])).

tff(c_36,plain,(
    ! [A_10,B_11,C_12,D_34] :
      ( '#skF_4'(A_10,B_11,C_12,D_34) = '#skF_3'(A_10,B_11,C_12,D_34)
      | ~ r1_partfun1(C_12,'#skF_5'(A_10,B_11,C_12,D_34))
      | ~ v1_partfun1('#skF_5'(A_10,B_11,C_12,D_34),A_10)
      | ~ m1_subset_1('#skF_5'(A_10,B_11,C_12,D_34),k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1('#skF_5'(A_10,B_11,C_12,D_34))
      | k5_partfun1(A_10,B_11,C_12) = D_34
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44280,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ r1_partfun1('#skF_9','#skF_10')
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_44062,c_36])).

tff(c_44445,plain,
    ( '#skF_4'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_44062,c_76,c_44062,c_193,c_44062,c_310,c_44280])).

tff(c_78833,plain,
    ( '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10'
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78554,c_44445])).

tff(c_78834,plain,(
    '#skF_3'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_77356,c_78833])).

tff(c_30,plain,(
    ! [A_10,B_11,C_12,D_34] :
      ( ~ r2_hidden('#skF_3'(A_10,B_11,C_12,D_34),D_34)
      | ~ r1_partfun1(C_12,'#skF_5'(A_10,B_11,C_12,D_34))
      | ~ v1_partfun1('#skF_5'(A_10,B_11,C_12,D_34),A_10)
      | ~ m1_subset_1('#skF_5'(A_10,B_11,C_12,D_34),k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1('#skF_5'(A_10,B_11,C_12,D_34))
      | k5_partfun1(A_10,B_11,C_12) = D_34
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78853,plain,
    ( ~ r2_hidden('#skF_10',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10'))
    | ~ r1_partfun1('#skF_9','#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | ~ v1_partfun1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),'#skF_7')
    | ~ m1_subset_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')),k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_5'('#skF_7',k1_tarski('#skF_8'),'#skF_9',k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10')))
    | k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))))
    | ~ v1_funct_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_78834,c_30])).

tff(c_78875,plain,(
    k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_10') = k5_partfun1('#skF_7',k1_tarski('#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_44062,c_76,c_44062,c_193,c_44062,c_310,c_44062,c_850,c_78853])).

tff(c_78877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77356,c_78875])).

%------------------------------------------------------------------------------
