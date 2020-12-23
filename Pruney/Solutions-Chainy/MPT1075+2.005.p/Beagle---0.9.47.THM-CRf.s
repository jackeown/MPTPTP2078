%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:11 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 212 expanded)
%              Number of leaves         :   38 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  222 ( 846 expanded)
%              Number of equality atoms :   38 ( 109 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_36,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_187,plain,(
    ! [A_100,B_101,C_102] :
      ( m1_subset_1(k2_relset_1(A_100,B_101,C_102),k1_zfmisc_1(B_101))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_223,plain,(
    ! [A_106,B_107,C_108] :
      ( r1_tarski(k2_relset_1(A_106,B_107,C_108),B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(resolution,[status(thm)],[c_187,c_4])).

tff(c_236,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_223])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_65,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_34,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_79,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_141,plain,(
    ! [B_95,A_96] :
      ( k1_relat_1(B_95) = A_96
      | ~ v1_partfun1(B_95,A_96)
      | ~ v4_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_144,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_141])).

tff(c_150,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_34,c_144])).

tff(c_164,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_174,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_164])).

tff(c_178,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_174])).

tff(c_663,plain,(
    ! [B_222,C_227,F_224,A_223,D_225,E_226] :
      ( k1_funct_1(k8_funct_2(B_222,C_227,A_223,D_225,E_226),F_224) = k1_funct_1(E_226,k1_funct_1(D_225,F_224))
      | k1_xboole_0 = B_222
      | ~ r1_tarski(k2_relset_1(B_222,C_227,D_225),k1_relset_1(C_227,A_223,E_226))
      | ~ m1_subset_1(F_224,B_222)
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(C_227,A_223)))
      | ~ v1_funct_1(E_226)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(k2_zfmisc_1(B_222,C_227)))
      | ~ v1_funct_2(D_225,B_222,C_227)
      | ~ v1_funct_1(D_225)
      | v1_xboole_0(C_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_667,plain,(
    ! [B_222,D_225,F_224] :
      ( k1_funct_1(k8_funct_2(B_222,'#skF_1','#skF_3',D_225,'#skF_5'),F_224) = k1_funct_1('#skF_5',k1_funct_1(D_225,F_224))
      | k1_xboole_0 = B_222
      | ~ r1_tarski(k2_relset_1(B_222,'#skF_1',D_225),'#skF_1')
      | ~ m1_subset_1(F_224,B_222)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_225,k1_zfmisc_1(k2_zfmisc_1(B_222,'#skF_1')))
      | ~ v1_funct_2(D_225,B_222,'#skF_1')
      | ~ v1_funct_1(D_225)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_663])).

tff(c_672,plain,(
    ! [B_222,D_225,F_224] :
      ( k1_funct_1(k8_funct_2(B_222,'#skF_1','#skF_3',D_225,'#skF_5'),F_224) = k1_funct_1('#skF_5',k1_funct_1(D_225,F_224))
      | k1_xboole_0 = B_222
      | ~ r1_tarski(k2_relset_1(B_222,'#skF_1',D_225),'#skF_1')
      | ~ m1_subset_1(F_224,B_222)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(k2_zfmisc_1(B_222,'#skF_1')))
      | ~ v1_funct_2(D_225,B_222,'#skF_1')
      | ~ v1_funct_1(D_225)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_667])).

tff(c_713,plain,(
    ! [B_238,D_239,F_240] :
      ( k1_funct_1(k8_funct_2(B_238,'#skF_1','#skF_3',D_239,'#skF_5'),F_240) = k1_funct_1('#skF_5',k1_funct_1(D_239,F_240))
      | k1_xboole_0 = B_238
      | ~ r1_tarski(k2_relset_1(B_238,'#skF_1',D_239),'#skF_1')
      | ~ m1_subset_1(F_240,B_238)
      | ~ m1_subset_1(D_239,k1_zfmisc_1(k2_zfmisc_1(B_238,'#skF_1')))
      | ~ v1_funct_2(D_239,B_238,'#skF_1')
      | ~ v1_funct_1(D_239) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_672])).

tff(c_724,plain,(
    ! [F_240] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_240) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_240))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_240,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_713])).

tff(c_730,plain,(
    ! [F_240] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_240) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_240))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_240,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_236,c_724])).

tff(c_742,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_730])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_745,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_2])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_745])).

tff(c_748,plain,(
    ! [F_240] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_240) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_240))
      | ~ m1_subset_1(F_240,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_730])).

tff(c_393,plain,(
    ! [B_159,D_160,A_158,E_161,C_157] :
      ( v1_funct_1(k8_funct_2(A_158,B_159,C_157,D_160,E_161))
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(B_159,C_157)))
      | ~ v1_funct_1(E_161)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_2(D_160,A_158,B_159)
      | ~ v1_funct_1(D_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_403,plain,(
    ! [A_158,D_160] :
      ( v1_funct_1(k8_funct_2(A_158,'#skF_1','#skF_3',D_160,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(A_158,'#skF_1')))
      | ~ v1_funct_2(D_160,A_158,'#skF_1')
      | ~ v1_funct_1(D_160) ) ),
    inference(resolution,[status(thm)],[c_38,c_393])).

tff(c_434,plain,(
    ! [A_166,D_167] :
      ( v1_funct_1(k8_funct_2(A_166,'#skF_1','#skF_3',D_167,'#skF_5'))
      | ~ m1_subset_1(D_167,k1_zfmisc_1(k2_zfmisc_1(A_166,'#skF_1')))
      | ~ v1_funct_2(D_167,A_166,'#skF_1')
      | ~ v1_funct_1(D_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_403])).

tff(c_445,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_434])).

tff(c_450,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_445])).

tff(c_479,plain,(
    ! [D_182,A_180,E_183,C_179,B_181] :
      ( v1_funct_2(k8_funct_2(A_180,B_181,C_179,D_182,E_183),A_180,C_179)
      | ~ m1_subset_1(E_183,k1_zfmisc_1(k2_zfmisc_1(B_181,C_179)))
      | ~ v1_funct_1(E_183)
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_2(D_182,A_180,B_181)
      | ~ v1_funct_1(D_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_489,plain,(
    ! [A_180,D_182] :
      ( v1_funct_2(k8_funct_2(A_180,'#skF_1','#skF_3',D_182,'#skF_5'),A_180,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(A_180,'#skF_1')))
      | ~ v1_funct_2(D_182,A_180,'#skF_1')
      | ~ v1_funct_1(D_182) ) ),
    inference(resolution,[status(thm)],[c_38,c_479])).

tff(c_508,plain,(
    ! [A_188,D_189] :
      ( v1_funct_2(k8_funct_2(A_188,'#skF_1','#skF_3',D_189,'#skF_5'),A_188,'#skF_3')
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(A_188,'#skF_1')))
      | ~ v1_funct_2(D_189,A_188,'#skF_1')
      | ~ v1_funct_1(D_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_489])).

tff(c_516,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_508])).

tff(c_521,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_516])).

tff(c_525,plain,(
    ! [B_199,E_201,C_197,A_198,D_200] :
      ( m1_subset_1(k8_funct_2(A_198,B_199,C_197,D_200,E_201),k1_zfmisc_1(k2_zfmisc_1(A_198,C_197)))
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(B_199,C_197)))
      | ~ v1_funct_1(E_201)
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_2(D_200,A_198,B_199)
      | ~ v1_funct_1(D_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_282,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( k3_funct_2(A_128,B_129,C_130,D_131) = k1_funct_1(C_130,D_131)
      | ~ m1_subset_1(D_131,A_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_2(C_130,A_128,B_129)
      | ~ v1_funct_1(C_130)
      | v1_xboole_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_292,plain,(
    ! [B_129,C_130] :
      ( k3_funct_2('#skF_2',B_129,C_130,'#skF_6') = k1_funct_1(C_130,'#skF_6')
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_129)))
      | ~ v1_funct_2(C_130,'#skF_2',B_129)
      | ~ v1_funct_1(C_130)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_282])).

tff(c_299,plain,(
    ! [B_129,C_130] :
      ( k3_funct_2('#skF_2',B_129,C_130,'#skF_6') = k1_funct_1(C_130,'#skF_6')
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_129)))
      | ~ v1_funct_2(C_130,'#skF_2',B_129)
      | ~ v1_funct_1(C_130) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_292])).

tff(c_1107,plain,(
    ! [C_339,B_340,D_341,E_342] :
      ( k3_funct_2('#skF_2',C_339,k8_funct_2('#skF_2',B_340,C_339,D_341,E_342),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2',B_340,C_339,D_341,E_342),'#skF_6')
      | ~ v1_funct_2(k8_funct_2('#skF_2',B_340,C_339,D_341,E_342),'#skF_2',C_339)
      | ~ v1_funct_1(k8_funct_2('#skF_2',B_340,C_339,D_341,E_342))
      | ~ m1_subset_1(E_342,k1_zfmisc_1(k2_zfmisc_1(B_340,C_339)))
      | ~ v1_funct_1(E_342)
      | ~ m1_subset_1(D_341,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_340)))
      | ~ v1_funct_2(D_341,'#skF_2',B_340)
      | ~ v1_funct_1(D_341) ) ),
    inference(resolution,[status(thm)],[c_525,c_299])).

tff(c_1117,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_521,c_1107])).

tff(c_1130,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_450,c_1117])).

tff(c_344,plain,(
    ! [B_144,C_145] :
      ( k3_funct_2('#skF_2',B_144,C_145,'#skF_6') = k1_funct_1(C_145,'#skF_6')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_144)))
      | ~ v1_funct_2(C_145,'#skF_2',B_144)
      | ~ v1_funct_1(C_145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_292])).

tff(c_355,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_344])).

tff(c_360,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_355])).

tff(c_32,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_361,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_32])).

tff(c_1134,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_361])).

tff(c_1141,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_1134])).

tff(c_1145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.62  
% 3.58/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.58/1.62  
% 3.58/1.62  %Foreground sorts:
% 3.58/1.62  
% 3.58/1.62  
% 3.58/1.62  %Background operators:
% 3.58/1.62  
% 3.58/1.62  
% 3.58/1.62  %Foreground operators:
% 3.58/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.58/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.58/1.62  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.58/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.58/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.62  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.58/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.58/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.58/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.58/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.58/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.62  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.58/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.58/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.62  
% 3.91/1.64  tff(f_136, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 3.91/1.64  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.91/1.64  tff(f_30, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.91/1.64  tff(f_34, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.91/1.64  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.91/1.64  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.91/1.64  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.91/1.64  tff(f_109, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.91/1.64  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.91/1.64  tff(f_72, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 3.91/1.64  tff(f_85, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.91/1.64  tff(c_36, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.64  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.64  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.64  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.64  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.64  tff(c_187, plain, (![A_100, B_101, C_102]: (m1_subset_1(k2_relset_1(A_100, B_101, C_102), k1_zfmisc_1(B_101)) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.91/1.64  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.91/1.64  tff(c_223, plain, (![A_106, B_107, C_108]: (r1_tarski(k2_relset_1(A_106, B_107, C_108), B_107) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(resolution, [status(thm)], [c_187, c_4])).
% 3.91/1.64  tff(c_236, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_42, c_223])).
% 3.91/1.64  tff(c_50, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.64  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.64  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.64  tff(c_65, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.91/1.64  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_65])).
% 3.91/1.64  tff(c_34, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.64  tff(c_79, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.91/1.64  tff(c_92, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_79])).
% 3.91/1.64  tff(c_141, plain, (![B_95, A_96]: (k1_relat_1(B_95)=A_96 | ~v1_partfun1(B_95, A_96) | ~v4_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.91/1.64  tff(c_144, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_141])).
% 3.91/1.64  tff(c_150, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_34, c_144])).
% 3.91/1.64  tff(c_164, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.91/1.64  tff(c_174, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_164])).
% 3.91/1.64  tff(c_178, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_174])).
% 3.91/1.64  tff(c_663, plain, (![B_222, C_227, F_224, A_223, D_225, E_226]: (k1_funct_1(k8_funct_2(B_222, C_227, A_223, D_225, E_226), F_224)=k1_funct_1(E_226, k1_funct_1(D_225, F_224)) | k1_xboole_0=B_222 | ~r1_tarski(k2_relset_1(B_222, C_227, D_225), k1_relset_1(C_227, A_223, E_226)) | ~m1_subset_1(F_224, B_222) | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(C_227, A_223))) | ~v1_funct_1(E_226) | ~m1_subset_1(D_225, k1_zfmisc_1(k2_zfmisc_1(B_222, C_227))) | ~v1_funct_2(D_225, B_222, C_227) | ~v1_funct_1(D_225) | v1_xboole_0(C_227))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.91/1.64  tff(c_667, plain, (![B_222, D_225, F_224]: (k1_funct_1(k8_funct_2(B_222, '#skF_1', '#skF_3', D_225, '#skF_5'), F_224)=k1_funct_1('#skF_5', k1_funct_1(D_225, F_224)) | k1_xboole_0=B_222 | ~r1_tarski(k2_relset_1(B_222, '#skF_1', D_225), '#skF_1') | ~m1_subset_1(F_224, B_222) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_225, k1_zfmisc_1(k2_zfmisc_1(B_222, '#skF_1'))) | ~v1_funct_2(D_225, B_222, '#skF_1') | ~v1_funct_1(D_225) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_663])).
% 3.91/1.64  tff(c_672, plain, (![B_222, D_225, F_224]: (k1_funct_1(k8_funct_2(B_222, '#skF_1', '#skF_3', D_225, '#skF_5'), F_224)=k1_funct_1('#skF_5', k1_funct_1(D_225, F_224)) | k1_xboole_0=B_222 | ~r1_tarski(k2_relset_1(B_222, '#skF_1', D_225), '#skF_1') | ~m1_subset_1(F_224, B_222) | ~m1_subset_1(D_225, k1_zfmisc_1(k2_zfmisc_1(B_222, '#skF_1'))) | ~v1_funct_2(D_225, B_222, '#skF_1') | ~v1_funct_1(D_225) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_667])).
% 3.91/1.64  tff(c_713, plain, (![B_238, D_239, F_240]: (k1_funct_1(k8_funct_2(B_238, '#skF_1', '#skF_3', D_239, '#skF_5'), F_240)=k1_funct_1('#skF_5', k1_funct_1(D_239, F_240)) | k1_xboole_0=B_238 | ~r1_tarski(k2_relset_1(B_238, '#skF_1', D_239), '#skF_1') | ~m1_subset_1(F_240, B_238) | ~m1_subset_1(D_239, k1_zfmisc_1(k2_zfmisc_1(B_238, '#skF_1'))) | ~v1_funct_2(D_239, B_238, '#skF_1') | ~v1_funct_1(D_239))), inference(negUnitSimplification, [status(thm)], [c_50, c_672])).
% 3.91/1.64  tff(c_724, plain, (![F_240]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_240)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_240)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_240, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_713])).
% 3.91/1.64  tff(c_730, plain, (![F_240]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_240)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_240)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_240, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_236, c_724])).
% 3.91/1.64  tff(c_742, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_730])).
% 3.91/1.64  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.91/1.64  tff(c_745, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_742, c_2])).
% 3.91/1.64  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_745])).
% 3.91/1.64  tff(c_748, plain, (![F_240]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_240)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_240)) | ~m1_subset_1(F_240, '#skF_2'))), inference(splitRight, [status(thm)], [c_730])).
% 3.91/1.64  tff(c_393, plain, (![B_159, D_160, A_158, E_161, C_157]: (v1_funct_1(k8_funct_2(A_158, B_159, C_157, D_160, E_161)) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(B_159, C_157))) | ~v1_funct_1(E_161) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_2(D_160, A_158, B_159) | ~v1_funct_1(D_160))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.91/1.64  tff(c_403, plain, (![A_158, D_160]: (v1_funct_1(k8_funct_2(A_158, '#skF_1', '#skF_3', D_160, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(A_158, '#skF_1'))) | ~v1_funct_2(D_160, A_158, '#skF_1') | ~v1_funct_1(D_160))), inference(resolution, [status(thm)], [c_38, c_393])).
% 3.91/1.64  tff(c_434, plain, (![A_166, D_167]: (v1_funct_1(k8_funct_2(A_166, '#skF_1', '#skF_3', D_167, '#skF_5')) | ~m1_subset_1(D_167, k1_zfmisc_1(k2_zfmisc_1(A_166, '#skF_1'))) | ~v1_funct_2(D_167, A_166, '#skF_1') | ~v1_funct_1(D_167))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_403])).
% 3.91/1.64  tff(c_445, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_434])).
% 3.91/1.64  tff(c_450, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_445])).
% 3.91/1.64  tff(c_479, plain, (![D_182, A_180, E_183, C_179, B_181]: (v1_funct_2(k8_funct_2(A_180, B_181, C_179, D_182, E_183), A_180, C_179) | ~m1_subset_1(E_183, k1_zfmisc_1(k2_zfmisc_1(B_181, C_179))) | ~v1_funct_1(E_183) | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_2(D_182, A_180, B_181) | ~v1_funct_1(D_182))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.91/1.64  tff(c_489, plain, (![A_180, D_182]: (v1_funct_2(k8_funct_2(A_180, '#skF_1', '#skF_3', D_182, '#skF_5'), A_180, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(A_180, '#skF_1'))) | ~v1_funct_2(D_182, A_180, '#skF_1') | ~v1_funct_1(D_182))), inference(resolution, [status(thm)], [c_38, c_479])).
% 3.91/1.64  tff(c_508, plain, (![A_188, D_189]: (v1_funct_2(k8_funct_2(A_188, '#skF_1', '#skF_3', D_189, '#skF_5'), A_188, '#skF_3') | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(A_188, '#skF_1'))) | ~v1_funct_2(D_189, A_188, '#skF_1') | ~v1_funct_1(D_189))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_489])).
% 3.91/1.64  tff(c_516, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_508])).
% 3.91/1.64  tff(c_521, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_516])).
% 3.91/1.64  tff(c_525, plain, (![B_199, E_201, C_197, A_198, D_200]: (m1_subset_1(k8_funct_2(A_198, B_199, C_197, D_200, E_201), k1_zfmisc_1(k2_zfmisc_1(A_198, C_197))) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(B_199, C_197))) | ~v1_funct_1(E_201) | ~m1_subset_1(D_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_2(D_200, A_198, B_199) | ~v1_funct_1(D_200))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.91/1.64  tff(c_282, plain, (![A_128, B_129, C_130, D_131]: (k3_funct_2(A_128, B_129, C_130, D_131)=k1_funct_1(C_130, D_131) | ~m1_subset_1(D_131, A_128) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_2(C_130, A_128, B_129) | ~v1_funct_1(C_130) | v1_xboole_0(A_128))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.91/1.64  tff(c_292, plain, (![B_129, C_130]: (k3_funct_2('#skF_2', B_129, C_130, '#skF_6')=k1_funct_1(C_130, '#skF_6') | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_129))) | ~v1_funct_2(C_130, '#skF_2', B_129) | ~v1_funct_1(C_130) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_282])).
% 3.91/1.64  tff(c_299, plain, (![B_129, C_130]: (k3_funct_2('#skF_2', B_129, C_130, '#skF_6')=k1_funct_1(C_130, '#skF_6') | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_129))) | ~v1_funct_2(C_130, '#skF_2', B_129) | ~v1_funct_1(C_130))), inference(negUnitSimplification, [status(thm)], [c_48, c_292])).
% 3.91/1.64  tff(c_1107, plain, (![C_339, B_340, D_341, E_342]: (k3_funct_2('#skF_2', C_339, k8_funct_2('#skF_2', B_340, C_339, D_341, E_342), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', B_340, C_339, D_341, E_342), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', B_340, C_339, D_341, E_342), '#skF_2', C_339) | ~v1_funct_1(k8_funct_2('#skF_2', B_340, C_339, D_341, E_342)) | ~m1_subset_1(E_342, k1_zfmisc_1(k2_zfmisc_1(B_340, C_339))) | ~v1_funct_1(E_342) | ~m1_subset_1(D_341, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_340))) | ~v1_funct_2(D_341, '#skF_2', B_340) | ~v1_funct_1(D_341))), inference(resolution, [status(thm)], [c_525, c_299])).
% 3.91/1.64  tff(c_1117, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_521, c_1107])).
% 3.91/1.64  tff(c_1130, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_450, c_1117])).
% 3.91/1.64  tff(c_344, plain, (![B_144, C_145]: (k3_funct_2('#skF_2', B_144, C_145, '#skF_6')=k1_funct_1(C_145, '#skF_6') | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_144))) | ~v1_funct_2(C_145, '#skF_2', B_144) | ~v1_funct_1(C_145))), inference(negUnitSimplification, [status(thm)], [c_48, c_292])).
% 3.91/1.64  tff(c_355, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_344])).
% 3.91/1.64  tff(c_360, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_355])).
% 3.91/1.64  tff(c_32, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.91/1.64  tff(c_361, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_360, c_32])).
% 3.91/1.64  tff(c_1134, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_361])).
% 3.91/1.64  tff(c_1141, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_748, c_1134])).
% 3.91/1.64  tff(c_1145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1141])).
% 3.91/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.64  
% 3.91/1.64  Inference rules
% 3.91/1.64  ----------------------
% 3.91/1.64  #Ref     : 0
% 3.91/1.64  #Sup     : 226
% 3.91/1.64  #Fact    : 0
% 3.91/1.64  #Define  : 0
% 3.91/1.64  #Split   : 6
% 3.91/1.64  #Chain   : 0
% 3.91/1.64  #Close   : 0
% 3.91/1.64  
% 3.91/1.64  Ordering : KBO
% 3.91/1.64  
% 3.91/1.64  Simplification rules
% 3.91/1.64  ----------------------
% 3.91/1.64  #Subsume      : 16
% 3.91/1.64  #Demod        : 101
% 3.91/1.64  #Tautology    : 27
% 3.91/1.64  #SimpNegUnit  : 5
% 3.91/1.64  #BackRed      : 5
% 3.91/1.64  
% 3.91/1.64  #Partial instantiations: 0
% 3.91/1.64  #Strategies tried      : 1
% 3.91/1.64  
% 3.91/1.64  Timing (in seconds)
% 3.91/1.64  ----------------------
% 3.91/1.65  Preprocessing        : 0.34
% 3.91/1.65  Parsing              : 0.18
% 3.91/1.65  CNF conversion       : 0.03
% 3.91/1.65  Main loop            : 0.52
% 3.91/1.65  Inferencing          : 0.20
% 3.91/1.65  Reduction            : 0.15
% 3.91/1.65  Demodulation         : 0.11
% 3.91/1.65  BG Simplification    : 0.03
% 3.91/1.65  Subsumption          : 0.10
% 3.91/1.65  Abstraction          : 0.03
% 3.91/1.65  MUC search           : 0.00
% 3.91/1.65  Cooper               : 0.00
% 3.91/1.65  Total                : 0.90
% 3.91/1.65  Index Insertion      : 0.00
% 3.91/1.65  Index Deletion       : 0.00
% 3.91/1.65  Index Matching       : 0.00
% 3.91/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
