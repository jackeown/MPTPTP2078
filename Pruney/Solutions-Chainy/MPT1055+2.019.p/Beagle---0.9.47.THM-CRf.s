%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:21 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 139 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :    6
%              Number of atoms          :  139 ( 381 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1033,plain,(
    ! [A_209,B_210,C_211,D_212] :
      ( k8_relset_1(A_209,B_210,C_211,D_212) = k10_relat_1(C_211,D_212)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1040,plain,(
    ! [D_212] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_212) = k10_relat_1('#skF_3',D_212) ),
    inference(resolution,[status(thm)],[c_42,c_1033])).

tff(c_12,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_85,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_95,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_85])).

tff(c_368,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k8_relset_1(A_110,B_111,C_112,D_113) = k10_relat_1(C_112,D_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_375,plain,(
    ! [D_113] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_113) = k10_relat_1('#skF_3',D_113) ),
    inference(resolution,[status(thm)],[c_42,c_368])).

tff(c_58,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_60,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_380,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_60])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_14,plain,(
    ! [C_13,A_11,B_12] :
      ( r1_tarski(k9_relat_1(C_13,A_11),k9_relat_1(C_13,B_12))
      | ~ r1_tarski(A_11,B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_178,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(k9_relat_1(B_78,k10_relat_1(B_78,A_79)),A_79)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_515,plain,(
    ! [A_139,A_140,B_141] :
      ( r1_tarski(A_139,A_140)
      | ~ r1_tarski(A_139,k9_relat_1(B_141,k10_relat_1(B_141,A_140)))
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141) ) ),
    inference(resolution,[status(thm)],[c_178,c_4])).

tff(c_526,plain,(
    ! [C_142,A_143,A_144] :
      ( r1_tarski(k9_relat_1(C_142,A_143),A_144)
      | ~ v1_funct_1(C_142)
      | ~ r1_tarski(A_143,k10_relat_1(C_142,A_144))
      | ~ v1_relat_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_14,c_515])).

tff(c_390,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( k7_relset_1(A_115,B_116,C_117,D_118) = k9_relat_1(C_117,D_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_397,plain,(
    ! [D_118] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_118) = k9_relat_1('#skF_3',D_118) ),
    inference(resolution,[status(thm)],[c_42,c_390])).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_100,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52])).

tff(c_412,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_100])).

tff(c_551,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_412])).

tff(c_595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_380,c_46,c_551])).

tff(c_596,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_617,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_52])).

tff(c_1041,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_617])).

tff(c_618,plain,(
    ! [B_149,A_150] :
      ( v1_relat_1(B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_150))
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_624,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_618])).

tff(c_634,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_624])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_598,plain,(
    ! [A_145,B_146] :
      ( r1_tarski(A_145,B_146)
      | ~ m1_subset_1(A_145,k1_zfmisc_1(B_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_610,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_598])).

tff(c_44,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_826,plain,(
    ! [A_175,B_176,C_177] :
      ( k1_relset_1(A_175,B_176,C_177) = k1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_835,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_826])).

tff(c_1503,plain,(
    ! [B_269,A_270,C_271] :
      ( k1_xboole_0 = B_269
      | k1_relset_1(A_270,B_269,C_271) = A_270
      | ~ v1_funct_2(C_271,A_270,B_269)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_270,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1510,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1503])).

tff(c_1514,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_835,c_1510])).

tff(c_1515,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1514])).

tff(c_861,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k7_relset_1(A_182,B_183,C_184,D_185) = k9_relat_1(C_184,D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_868,plain,(
    ! [D_185] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_185) = k9_relat_1('#skF_3',D_185) ),
    inference(resolution,[status(thm)],[c_42,c_861])).

tff(c_872,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_596])).

tff(c_1882,plain,(
    ! [A_303,C_304,B_305] :
      ( r1_tarski(A_303,k10_relat_1(C_304,B_305))
      | ~ r1_tarski(k9_relat_1(C_304,A_303),B_305)
      | ~ r1_tarski(A_303,k1_relat_1(C_304))
      | ~ v1_funct_1(C_304)
      | ~ v1_relat_1(C_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1933,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_872,c_1882])).

tff(c_1975,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_46,c_610,c_1515,c_1933])).

tff(c_1977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1041,c_1975])).

tff(c_1978,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1514])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1989,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1978,c_2])).

tff(c_1991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1989])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.77  
% 4.41/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.77  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.41/1.77  
% 4.41/1.77  %Foreground sorts:
% 4.41/1.77  
% 4.41/1.77  
% 4.41/1.77  %Background operators:
% 4.41/1.77  
% 4.41/1.77  
% 4.41/1.77  %Foreground operators:
% 4.41/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.41/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.77  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.41/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.41/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.41/1.77  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.41/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.41/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.41/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.41/1.77  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.41/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.41/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.41/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.41/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.41/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.78  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.41/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.41/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.41/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.41/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.41/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.41/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.41/1.78  
% 4.41/1.79  tff(f_122, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 4.41/1.79  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.41/1.79  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.41/1.79  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.41/1.79  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 4.41/1.79  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 4.41/1.79  tff(f_32, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.41/1.79  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.41/1.79  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.41/1.79  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.41/1.79  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.41/1.79  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.41/1.79  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.41/1.79  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.41/1.79  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.41/1.79  tff(c_1033, plain, (![A_209, B_210, C_211, D_212]: (k8_relset_1(A_209, B_210, C_211, D_212)=k10_relat_1(C_211, D_212) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.41/1.79  tff(c_1040, plain, (![D_212]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_212)=k10_relat_1('#skF_3', D_212))), inference(resolution, [status(thm)], [c_42, c_1033])).
% 4.41/1.79  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.41/1.79  tff(c_79, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.41/1.79  tff(c_85, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_79])).
% 4.41/1.79  tff(c_95, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_85])).
% 4.41/1.79  tff(c_368, plain, (![A_110, B_111, C_112, D_113]: (k8_relset_1(A_110, B_111, C_112, D_113)=k10_relat_1(C_112, D_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.41/1.79  tff(c_375, plain, (![D_113]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_113)=k10_relat_1('#skF_3', D_113))), inference(resolution, [status(thm)], [c_42, c_368])).
% 4.41/1.79  tff(c_58, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.41/1.79  tff(c_60, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_58])).
% 4.41/1.79  tff(c_380, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_375, c_60])).
% 4.41/1.79  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.41/1.79  tff(c_14, plain, (![C_13, A_11, B_12]: (r1_tarski(k9_relat_1(C_13, A_11), k9_relat_1(C_13, B_12)) | ~r1_tarski(A_11, B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.41/1.79  tff(c_178, plain, (![B_78, A_79]: (r1_tarski(k9_relat_1(B_78, k10_relat_1(B_78, A_79)), A_79) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.41/1.79  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.41/1.79  tff(c_515, plain, (![A_139, A_140, B_141]: (r1_tarski(A_139, A_140) | ~r1_tarski(A_139, k9_relat_1(B_141, k10_relat_1(B_141, A_140))) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141))), inference(resolution, [status(thm)], [c_178, c_4])).
% 4.41/1.79  tff(c_526, plain, (![C_142, A_143, A_144]: (r1_tarski(k9_relat_1(C_142, A_143), A_144) | ~v1_funct_1(C_142) | ~r1_tarski(A_143, k10_relat_1(C_142, A_144)) | ~v1_relat_1(C_142))), inference(resolution, [status(thm)], [c_14, c_515])).
% 4.41/1.79  tff(c_390, plain, (![A_115, B_116, C_117, D_118]: (k7_relset_1(A_115, B_116, C_117, D_118)=k9_relat_1(C_117, D_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.41/1.79  tff(c_397, plain, (![D_118]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_118)=k9_relat_1('#skF_3', D_118))), inference(resolution, [status(thm)], [c_42, c_390])).
% 4.41/1.79  tff(c_52, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.41/1.79  tff(c_100, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52])).
% 4.41/1.79  tff(c_412, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_397, c_100])).
% 4.41/1.79  tff(c_551, plain, (~v1_funct_1('#skF_3') | ~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_526, c_412])).
% 4.41/1.79  tff(c_595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_380, c_46, c_551])).
% 4.41/1.79  tff(c_596, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 4.41/1.79  tff(c_617, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_596, c_52])).
% 4.41/1.79  tff(c_1041, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_617])).
% 4.41/1.79  tff(c_618, plain, (![B_149, A_150]: (v1_relat_1(B_149) | ~m1_subset_1(B_149, k1_zfmisc_1(A_150)) | ~v1_relat_1(A_150))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.41/1.79  tff(c_624, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_618])).
% 4.41/1.79  tff(c_634, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_624])).
% 4.41/1.79  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.41/1.79  tff(c_598, plain, (![A_145, B_146]: (r1_tarski(A_145, B_146) | ~m1_subset_1(A_145, k1_zfmisc_1(B_146)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.41/1.79  tff(c_610, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_598])).
% 4.41/1.79  tff(c_44, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.41/1.79  tff(c_826, plain, (![A_175, B_176, C_177]: (k1_relset_1(A_175, B_176, C_177)=k1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.41/1.79  tff(c_835, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_826])).
% 4.41/1.79  tff(c_1503, plain, (![B_269, A_270, C_271]: (k1_xboole_0=B_269 | k1_relset_1(A_270, B_269, C_271)=A_270 | ~v1_funct_2(C_271, A_270, B_269) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_270, B_269))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.41/1.79  tff(c_1510, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_1503])).
% 4.41/1.79  tff(c_1514, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_835, c_1510])).
% 4.41/1.79  tff(c_1515, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1514])).
% 4.41/1.79  tff(c_861, plain, (![A_182, B_183, C_184, D_185]: (k7_relset_1(A_182, B_183, C_184, D_185)=k9_relat_1(C_184, D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.41/1.79  tff(c_868, plain, (![D_185]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_185)=k9_relat_1('#skF_3', D_185))), inference(resolution, [status(thm)], [c_42, c_861])).
% 4.41/1.79  tff(c_872, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_868, c_596])).
% 4.41/1.79  tff(c_1882, plain, (![A_303, C_304, B_305]: (r1_tarski(A_303, k10_relat_1(C_304, B_305)) | ~r1_tarski(k9_relat_1(C_304, A_303), B_305) | ~r1_tarski(A_303, k1_relat_1(C_304)) | ~v1_funct_1(C_304) | ~v1_relat_1(C_304))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.41/1.79  tff(c_1933, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_872, c_1882])).
% 4.41/1.79  tff(c_1975, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_634, c_46, c_610, c_1515, c_1933])).
% 4.41/1.79  tff(c_1977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1041, c_1975])).
% 4.41/1.79  tff(c_1978, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1514])).
% 4.41/1.79  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.41/1.79  tff(c_1989, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1978, c_2])).
% 4.41/1.79  tff(c_1991, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1989])).
% 4.41/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.79  
% 4.41/1.79  Inference rules
% 4.41/1.79  ----------------------
% 4.41/1.79  #Ref     : 0
% 4.41/1.79  #Sup     : 461
% 4.41/1.79  #Fact    : 0
% 4.41/1.79  #Define  : 0
% 4.41/1.79  #Split   : 21
% 4.41/1.79  #Chain   : 0
% 4.41/1.79  #Close   : 0
% 4.41/1.79  
% 4.41/1.79  Ordering : KBO
% 4.41/1.79  
% 4.41/1.79  Simplification rules
% 4.41/1.79  ----------------------
% 4.41/1.79  #Subsume      : 118
% 4.41/1.79  #Demod        : 120
% 4.41/1.79  #Tautology    : 41
% 4.41/1.79  #SimpNegUnit  : 2
% 4.41/1.79  #BackRed      : 22
% 4.41/1.79  
% 4.41/1.79  #Partial instantiations: 0
% 4.41/1.79  #Strategies tried      : 1
% 4.41/1.79  
% 4.41/1.79  Timing (in seconds)
% 4.41/1.79  ----------------------
% 4.41/1.79  Preprocessing        : 0.33
% 4.41/1.79  Parsing              : 0.17
% 4.41/1.79  CNF conversion       : 0.03
% 4.41/1.79  Main loop            : 0.65
% 4.41/1.79  Inferencing          : 0.21
% 4.41/1.79  Reduction            : 0.20
% 4.41/1.79  Demodulation         : 0.13
% 4.41/1.79  BG Simplification    : 0.03
% 4.41/1.79  Subsumption          : 0.16
% 4.41/1.79  Abstraction          : 0.03
% 4.41/1.80  MUC search           : 0.00
% 4.41/1.80  Cooper               : 0.00
% 4.41/1.80  Total                : 1.01
% 4.41/1.80  Index Insertion      : 0.00
% 4.41/1.80  Index Deletion       : 0.00
% 4.41/1.80  Index Matching       : 0.00
% 4.41/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
