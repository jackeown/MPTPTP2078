%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:21 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 173 expanded)
%              Number of leaves         :   35 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  154 ( 484 expanded)
%              Number of equality atoms :   21 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_116,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_763,plain,(
    ! [A_154,B_155] :
      ( r1_tarski(A_154,B_155)
      | ~ m1_subset_1(A_154,k1_zfmisc_1(B_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_775,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_763])).

tff(c_12,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_781,plain,(
    ! [B_158,A_159] :
      ( v1_relat_1(B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_159))
      | ~ v1_relat_1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_787,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_781])).

tff(c_797,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_787])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1102,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( k8_relset_1(A_198,B_199,C_200,D_201) = k10_relat_1(C_200,D_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1109,plain,(
    ! [D_201] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_201) = k10_relat_1('#skF_3',D_201) ),
    inference(resolution,[status(thm)],[c_34,c_1102])).

tff(c_1017,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( k7_relset_1(A_191,B_192,C_193,D_194) = k9_relat_1(C_193,D_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1024,plain,(
    ! [D_194] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_194) = k9_relat_1('#skF_3',D_194) ),
    inference(resolution,[status(thm)],[c_34,c_1017])).

tff(c_1381,plain,(
    ! [B_239,A_240,C_241] :
      ( k1_xboole_0 = B_239
      | k8_relset_1(A_240,B_239,C_241,k7_relset_1(A_240,B_239,C_241,A_240)) = A_240
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_240,B_239)))
      | ~ v1_funct_2(C_241,A_240,B_239)
      | ~ v1_funct_1(C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1386,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1381])).

tff(c_1390,plain,
    ( k1_xboole_0 = '#skF_2'
    | k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1109,c_1024,c_1386])).

tff(c_1391,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1390])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k10_relat_1(B_15,A_14),k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_827,plain,(
    ! [A_164,C_165,B_166] :
      ( r1_tarski(A_164,C_165)
      | ~ r1_tarski(B_166,C_165)
      | ~ r1_tarski(A_164,B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_838,plain,(
    ! [A_164,B_15,A_14] :
      ( r1_tarski(A_164,k1_relat_1(B_15))
      | ~ r1_tarski(A_164,k10_relat_1(B_15,A_14))
      | ~ v1_relat_1(B_15) ) ),
    inference(resolution,[status(thm)],[c_16,c_827])).

tff(c_1401,plain,(
    ! [A_164] :
      ( r1_tarski(A_164,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_164,'#skF_1')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1391,c_838])).

tff(c_1447,plain,(
    ! [A_244] :
      ( r1_tarski(A_244,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_244,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_1401])).

tff(c_72,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_72])).

tff(c_88,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_78])).

tff(c_295,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k8_relset_1(A_98,B_99,C_100,D_101) = k10_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_302,plain,(
    ! [D_101] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_101) = k10_relat_1('#skF_3',D_101) ),
    inference(resolution,[status(thm)],[c_34,c_295])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_52,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_91,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50])).

tff(c_306,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_91])).

tff(c_14,plain,(
    ! [C_13,A_11,B_12] :
      ( r1_tarski(k9_relat_1(C_13,A_11),k9_relat_1(C_13,B_12))
      | ~ r1_tarski(A_11,B_12)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_180,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(k9_relat_1(B_81,k10_relat_1(B_81,A_82)),A_82)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_662,plain,(
    ! [A_144,A_145,B_146] :
      ( r1_tarski(A_144,A_145)
      | ~ r1_tarski(A_144,k9_relat_1(B_146,k10_relat_1(B_146,A_145)))
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_180,c_4])).

tff(c_673,plain,(
    ! [C_147,A_148,A_149] :
      ( r1_tarski(k9_relat_1(C_147,A_148),A_149)
      | ~ v1_funct_1(C_147)
      | ~ r1_tarski(A_148,k10_relat_1(C_147,A_149))
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_14,c_662])).

tff(c_390,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k7_relset_1(A_105,B_106,C_107,D_108) = k9_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_397,plain,(
    ! [D_108] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_108) = k9_relat_1('#skF_3',D_108) ),
    inference(resolution,[status(thm)],[c_34,c_390])).

tff(c_398,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_52])).

tff(c_703,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_673,c_398])).

tff(c_737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_306,c_38,c_703])).

tff(c_738,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_740,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_738,c_740])).

tff(c_761,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1110,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_761])).

tff(c_739,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1028,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_739])).

tff(c_1178,plain,(
    ! [A_211,C_212,B_213] :
      ( r1_tarski(A_211,k10_relat_1(C_212,B_213))
      | ~ r1_tarski(k9_relat_1(C_212,A_211),B_213)
      | ~ r1_tarski(A_211,k1_relat_1(C_212))
      | ~ v1_funct_1(C_212)
      | ~ v1_relat_1(C_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1190,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1028,c_1178])).

tff(c_1219,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_38,c_1190])).

tff(c_1220,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1110,c_1219])).

tff(c_1450,plain,(
    ~ r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1447,c_1220])).

tff(c_1467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_1450])).

tff(c_1468,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1390])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1472,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_2])).

tff(c_1474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:31:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.61  
% 3.49/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.61  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.49/1.61  
% 3.49/1.61  %Foreground sorts:
% 3.49/1.61  
% 3.49/1.61  
% 3.49/1.61  %Background operators:
% 3.49/1.61  
% 3.49/1.61  
% 3.49/1.61  %Foreground operators:
% 3.49/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.49/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.49/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.49/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.49/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.61  
% 3.49/1.63  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 3.49/1.63  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.49/1.63  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.49/1.63  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.49/1.63  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.49/1.63  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.49/1.63  tff(f_91, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_2)).
% 3.49/1.63  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 3.49/1.63  tff(f_32, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.49/1.63  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 3.49/1.63  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 3.49/1.63  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 3.49/1.63  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.49/1.63  tff(c_40, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.63  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.63  tff(c_763, plain, (![A_154, B_155]: (r1_tarski(A_154, B_155) | ~m1_subset_1(A_154, k1_zfmisc_1(B_155)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.49/1.63  tff(c_775, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_763])).
% 3.49/1.63  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.49/1.63  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.63  tff(c_781, plain, (![B_158, A_159]: (v1_relat_1(B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(A_159)) | ~v1_relat_1(A_159))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.49/1.63  tff(c_787, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_781])).
% 3.49/1.63  tff(c_797, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_787])).
% 3.49/1.63  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.63  tff(c_36, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.63  tff(c_1102, plain, (![A_198, B_199, C_200, D_201]: (k8_relset_1(A_198, B_199, C_200, D_201)=k10_relat_1(C_200, D_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.63  tff(c_1109, plain, (![D_201]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_201)=k10_relat_1('#skF_3', D_201))), inference(resolution, [status(thm)], [c_34, c_1102])).
% 3.49/1.63  tff(c_1017, plain, (![A_191, B_192, C_193, D_194]: (k7_relset_1(A_191, B_192, C_193, D_194)=k9_relat_1(C_193, D_194) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.49/1.63  tff(c_1024, plain, (![D_194]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_194)=k9_relat_1('#skF_3', D_194))), inference(resolution, [status(thm)], [c_34, c_1017])).
% 3.49/1.63  tff(c_1381, plain, (![B_239, A_240, C_241]: (k1_xboole_0=B_239 | k8_relset_1(A_240, B_239, C_241, k7_relset_1(A_240, B_239, C_241, A_240))=A_240 | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_240, B_239))) | ~v1_funct_2(C_241, A_240, B_239) | ~v1_funct_1(C_241))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.49/1.63  tff(c_1386, plain, (k1_xboole_0='#skF_2' | k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1381])).
% 3.49/1.63  tff(c_1390, plain, (k1_xboole_0='#skF_2' | k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1109, c_1024, c_1386])).
% 3.49/1.63  tff(c_1391, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(splitLeft, [status(thm)], [c_1390])).
% 3.49/1.63  tff(c_16, plain, (![B_15, A_14]: (r1_tarski(k10_relat_1(B_15, A_14), k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.49/1.63  tff(c_827, plain, (![A_164, C_165, B_166]: (r1_tarski(A_164, C_165) | ~r1_tarski(B_166, C_165) | ~r1_tarski(A_164, B_166))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.49/1.63  tff(c_838, plain, (![A_164, B_15, A_14]: (r1_tarski(A_164, k1_relat_1(B_15)) | ~r1_tarski(A_164, k10_relat_1(B_15, A_14)) | ~v1_relat_1(B_15))), inference(resolution, [status(thm)], [c_16, c_827])).
% 3.49/1.63  tff(c_1401, plain, (![A_164]: (r1_tarski(A_164, k1_relat_1('#skF_3')) | ~r1_tarski(A_164, '#skF_1') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1391, c_838])).
% 3.49/1.63  tff(c_1447, plain, (![A_244]: (r1_tarski(A_244, k1_relat_1('#skF_3')) | ~r1_tarski(A_244, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_797, c_1401])).
% 3.49/1.63  tff(c_72, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.49/1.63  tff(c_78, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_72])).
% 3.49/1.63  tff(c_88, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_78])).
% 3.49/1.63  tff(c_295, plain, (![A_98, B_99, C_100, D_101]: (k8_relset_1(A_98, B_99, C_100, D_101)=k10_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.63  tff(c_302, plain, (![D_101]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_101)=k10_relat_1('#skF_3', D_101))), inference(resolution, [status(thm)], [c_34, c_295])).
% 3.49/1.63  tff(c_44, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.63  tff(c_52, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 3.49/1.63  tff(c_50, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.63  tff(c_91, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_50])).
% 3.49/1.63  tff(c_306, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_91])).
% 3.49/1.63  tff(c_14, plain, (![C_13, A_11, B_12]: (r1_tarski(k9_relat_1(C_13, A_11), k9_relat_1(C_13, B_12)) | ~r1_tarski(A_11, B_12) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.49/1.63  tff(c_180, plain, (![B_81, A_82]: (r1_tarski(k9_relat_1(B_81, k10_relat_1(B_81, A_82)), A_82) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.49/1.63  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.49/1.63  tff(c_662, plain, (![A_144, A_145, B_146]: (r1_tarski(A_144, A_145) | ~r1_tarski(A_144, k9_relat_1(B_146, k10_relat_1(B_146, A_145))) | ~v1_funct_1(B_146) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_180, c_4])).
% 3.49/1.63  tff(c_673, plain, (![C_147, A_148, A_149]: (r1_tarski(k9_relat_1(C_147, A_148), A_149) | ~v1_funct_1(C_147) | ~r1_tarski(A_148, k10_relat_1(C_147, A_149)) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_14, c_662])).
% 3.49/1.63  tff(c_390, plain, (![A_105, B_106, C_107, D_108]: (k7_relset_1(A_105, B_106, C_107, D_108)=k9_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.49/1.63  tff(c_397, plain, (![D_108]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_108)=k9_relat_1('#skF_3', D_108))), inference(resolution, [status(thm)], [c_34, c_390])).
% 3.49/1.63  tff(c_398, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_397, c_52])).
% 3.49/1.63  tff(c_703, plain, (~v1_funct_1('#skF_3') | ~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_673, c_398])).
% 3.49/1.63  tff(c_737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_306, c_38, c_703])).
% 3.49/1.63  tff(c_738, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_44])).
% 3.49/1.63  tff(c_740, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.49/1.63  tff(c_759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_738, c_740])).
% 3.49/1.63  tff(c_761, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_50])).
% 3.49/1.63  tff(c_1110, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_761])).
% 3.49/1.63  tff(c_739, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 3.49/1.63  tff(c_1028, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1024, c_739])).
% 3.49/1.63  tff(c_1178, plain, (![A_211, C_212, B_213]: (r1_tarski(A_211, k10_relat_1(C_212, B_213)) | ~r1_tarski(k9_relat_1(C_212, A_211), B_213) | ~r1_tarski(A_211, k1_relat_1(C_212)) | ~v1_funct_1(C_212) | ~v1_relat_1(C_212))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.49/1.63  tff(c_1190, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1028, c_1178])).
% 3.49/1.63  tff(c_1219, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_797, c_38, c_1190])).
% 3.49/1.63  tff(c_1220, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1110, c_1219])).
% 3.49/1.63  tff(c_1450, plain, (~r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1447, c_1220])).
% 3.49/1.63  tff(c_1467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_775, c_1450])).
% 3.49/1.63  tff(c_1468, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1390])).
% 3.49/1.63  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.49/1.63  tff(c_1472, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1468, c_2])).
% 3.49/1.63  tff(c_1474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1472])).
% 3.49/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.63  
% 3.49/1.63  Inference rules
% 3.49/1.63  ----------------------
% 3.49/1.63  #Ref     : 0
% 3.49/1.63  #Sup     : 341
% 3.49/1.63  #Fact    : 0
% 3.49/1.63  #Define  : 0
% 3.49/1.63  #Split   : 22
% 3.49/1.63  #Chain   : 0
% 3.49/1.63  #Close   : 0
% 3.49/1.63  
% 3.49/1.63  Ordering : KBO
% 3.49/1.63  
% 3.49/1.63  Simplification rules
% 3.49/1.63  ----------------------
% 3.49/1.63  #Subsume      : 100
% 3.49/1.63  #Demod        : 85
% 3.49/1.63  #Tautology    : 40
% 3.49/1.63  #SimpNegUnit  : 6
% 3.49/1.63  #BackRed      : 13
% 3.49/1.63  
% 3.49/1.63  #Partial instantiations: 0
% 3.49/1.63  #Strategies tried      : 1
% 3.49/1.63  
% 3.49/1.63  Timing (in seconds)
% 3.49/1.63  ----------------------
% 3.49/1.63  Preprocessing        : 0.33
% 3.49/1.63  Parsing              : 0.18
% 3.49/1.63  CNF conversion       : 0.03
% 3.49/1.63  Main loop            : 0.51
% 3.49/1.63  Inferencing          : 0.18
% 3.49/1.63  Reduction            : 0.15
% 3.49/1.63  Demodulation         : 0.10
% 3.49/1.63  BG Simplification    : 0.02
% 3.49/1.63  Subsumption          : 0.11
% 3.49/1.63  Abstraction          : 0.03
% 3.49/1.63  MUC search           : 0.00
% 3.49/1.63  Cooper               : 0.00
% 3.49/1.63  Total                : 0.89
% 3.49/1.63  Index Insertion      : 0.00
% 3.49/1.63  Index Deletion       : 0.00
% 3.49/1.63  Index Matching       : 0.00
% 3.49/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
