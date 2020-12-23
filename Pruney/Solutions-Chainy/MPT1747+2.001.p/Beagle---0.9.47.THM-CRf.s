%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:49 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  129 (1665 expanded)
%              Number of leaves         :   36 ( 601 expanded)
%              Depth                    :   18
%              Number of atoms          :  364 (8213 expanded)
%              Number of equality atoms :   29 (1045 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( ( u1_struct_0(B) = u1_struct_0(C)
                    & r1_tarski(u1_pre_topc(C),u1_pre_topc(B)) )
                 => ! [D] :
                      ( ( v1_funct_1(D)
                        & v1_funct_2(D,u1_struct_0(A),u1_struct_0(B))
                        & v5_pre_topc(D,A,B)
                        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ( v1_funct_1(D)
                        & v1_funct_2(D,u1_struct_0(A),u1_struct_0(C))
                        & v5_pre_topc(D,A,C)
                        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_struct_0(B) = k1_xboole_0
                 => k2_struct_0(A) = k1_xboole_0 )
               => ( v5_pre_topc(C,A,B)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( v3_pre_topc(D,B)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_68,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_48,c_38,c_48,c_36])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_16,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_74,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_16,c_74])).

tff(c_90,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_79])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_89,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_79])).

tff(c_93,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_42])).

tff(c_160,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_93])).

tff(c_92,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_38])).

tff(c_168,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_92])).

tff(c_50,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_94,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_48])).

tff(c_91,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_79])).

tff(c_107,plain,(
    k2_struct_0('#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_91])).

tff(c_257,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_struct_0(A_82) != k1_xboole_0
      | v3_pre_topc('#skF_2'(A_82,B_83,C_84),B_83)
      | v5_pre_topc(C_84,A_82,B_83)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_82),u1_struct_0(B_83))))
      | ~ v1_funct_2(C_84,u1_struct_0(A_82),u1_struct_0(B_83))
      | ~ v1_funct_1(C_84)
      | ~ l1_pre_topc(B_83)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_259,plain,(
    ! [B_83,C_84] :
      ( k2_struct_0('#skF_5') != k1_xboole_0
      | v3_pre_topc('#skF_2'('#skF_5',B_83,C_84),B_83)
      | v5_pre_topc(C_84,'#skF_5',B_83)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_83))))
      | ~ v1_funct_2(C_84,u1_struct_0('#skF_5'),u1_struct_0(B_83))
      | ~ v1_funct_1(C_84)
      | ~ l1_pre_topc(B_83)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_257])).

tff(c_271,plain,(
    ! [B_83,C_84] :
      ( k2_struct_0('#skF_4') != k1_xboole_0
      | v3_pre_topc('#skF_2'('#skF_5',B_83,C_84),B_83)
      | v5_pre_topc(C_84,'#skF_5',B_83)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_83))))
      | ~ v1_funct_2(C_84,k2_struct_0('#skF_4'),u1_struct_0(B_83))
      | ~ v1_funct_1(C_84)
      | ~ l1_pre_topc(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_94,c_107,c_259])).

tff(c_289,plain,(
    k2_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_418,plain,(
    ! [B_108,A_109,C_110] :
      ( k2_struct_0(B_108) = k1_xboole_0
      | m1_subset_1('#skF_2'(A_109,B_108,C_110),k1_zfmisc_1(u1_struct_0(B_108)))
      | v5_pre_topc(C_110,A_109,B_108)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109),u1_struct_0(B_108))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_109),u1_struct_0(B_108))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc(B_108)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_422,plain,(
    ! [A_109,C_110] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | m1_subset_1('#skF_2'(A_109,'#skF_5',C_110),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v5_pre_topc(C_110,A_109,'#skF_5')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_109),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_418])).

tff(c_434,plain,(
    ! [A_109,C_110] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | m1_subset_1('#skF_2'(A_109,'#skF_5',C_110),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(C_110,A_109,'#skF_5')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_109),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_94,c_94,c_107,c_422])).

tff(c_484,plain,(
    ! [A_121,C_122] :
      ( m1_subset_1('#skF_2'(A_121,'#skF_5',C_122),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(C_122,A_121,'#skF_5')
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_121),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_122,u1_struct_0(A_121),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_122)
      | ~ l1_pre_topc(A_121) ) ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_434])).

tff(c_490,plain,(
    ! [C_122] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5',C_122),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(C_122,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_122,u1_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_122)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_484])).

tff(c_526,plain,(
    ! [C_127] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5',C_127),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(C_127,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_127,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_90,c_490])).

tff(c_529,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v5_pre_topc('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_168,c_526])).

tff(c_532,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v5_pre_topc('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_160,c_529])).

tff(c_533,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_532])).

tff(c_46,plain,(
    r1_tarski(u1_pre_topc('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_339,plain,(
    ! [B_95,A_96,C_97] :
      ( k2_struct_0(B_95) = k1_xboole_0
      | v3_pre_topc('#skF_2'(A_96,B_95,C_97),B_95)
      | v5_pre_topc(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96),u1_struct_0(B_95))))
      | ~ v1_funct_2(C_97,u1_struct_0(A_96),u1_struct_0(B_95))
      | ~ v1_funct_1(C_97)
      | ~ l1_pre_topc(B_95)
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_343,plain,(
    ! [A_96,C_97] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | v3_pre_topc('#skF_2'(A_96,'#skF_5',C_97),'#skF_5')
      | v5_pre_topc(C_97,A_96,'#skF_5')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_97,u1_struct_0(A_96),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_97)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_339])).

tff(c_355,plain,(
    ! [A_96,C_97] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc('#skF_2'(A_96,'#skF_5',C_97),'#skF_5')
      | v5_pre_topc(C_97,A_96,'#skF_5')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_97,u1_struct_0(A_96),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_97)
      | ~ l1_pre_topc(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_94,c_107,c_343])).

tff(c_367,plain,(
    ! [A_98,C_99] :
      ( v3_pre_topc('#skF_2'(A_98,'#skF_5',C_99),'#skF_5')
      | v5_pre_topc(C_99,A_98,'#skF_5')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_99,u1_struct_0(A_98),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_99)
      | ~ l1_pre_topc(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_355])).

tff(c_373,plain,(
    ! [C_99] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5',C_99),'#skF_5')
      | v5_pre_topc(C_99,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_99,u1_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_99)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_367])).

tff(c_384,plain,(
    ! [C_101] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5',C_101),'#skF_5')
      | v5_pre_topc(C_101,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_101,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_90,c_373])).

tff(c_387,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_5')
    | v5_pre_topc('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_168,c_384])).

tff(c_390,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_5')
    | v5_pre_topc('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_160,c_387])).

tff(c_391,plain,(
    v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_390])).

tff(c_200,plain,(
    ! [B_64,A_65] :
      ( r2_hidden(B_64,u1_pre_topc(A_65))
      | ~ v3_pre_topc(B_64,A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_203,plain,(
    ! [B_64] :
      ( r2_hidden(B_64,u1_pre_topc('#skF_5'))
      | ~ v3_pre_topc(B_64,'#skF_5')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_200])).

tff(c_211,plain,(
    ! [B_64] :
      ( r2_hidden(B_64,u1_pre_topc('#skF_5'))
      | ~ v3_pre_topc(B_64,'#skF_5')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_203])).

tff(c_539,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_5','#skF_6'),u1_pre_topc('#skF_5'))
    | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_533,c_211])).

tff(c_549,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_5','#skF_6'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_539])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_556,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_5','#skF_6'),B_2)
      | ~ r1_tarski(u1_pre_topc('#skF_5'),B_2) ) ),
    inference(resolution,[status(thm)],[c_549,c_2])).

tff(c_209,plain,(
    ! [B_64] :
      ( r2_hidden(B_64,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(B_64,'#skF_4')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_200])).

tff(c_215,plain,(
    ! [B_64] :
      ( r2_hidden(B_64,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(B_64,'#skF_4')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_209])).

tff(c_546,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_5','#skF_6'),u1_pre_topc('#skF_4'))
    | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_533,c_215])).

tff(c_553,plain,(
    ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_182,plain,(
    ! [B_60,A_61] :
      ( v3_pre_topc(B_60,A_61)
      | ~ r2_hidden(B_60,u1_pre_topc(A_61))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_191,plain,(
    ! [B_60] :
      ( v3_pre_topc(B_60,'#skF_4')
      | ~ r2_hidden(B_60,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_182])).

tff(c_197,plain,(
    ! [B_60] :
      ( v3_pre_topc(B_60,'#skF_4')
      | ~ r2_hidden(B_60,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_191])).

tff(c_550,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_5','#skF_6'),u1_pre_topc('#skF_4')) ),
    inference(resolution,[status(thm)],[c_533,c_197])).

tff(c_561,plain,(
    ~ r2_hidden('#skF_2'('#skF_3','#skF_5','#skF_6'),u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_553,c_550])).

tff(c_564,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(resolution,[status(thm)],[c_556,c_561])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_564])).

tff(c_570,plain,(
    v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_40,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_775,plain,(
    ! [B_157,A_158,C_159,D_160] :
      ( k2_struct_0(B_157) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_158),u1_struct_0(B_157),C_159,D_160),A_158)
      | ~ v3_pre_topc(D_160,B_157)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(u1_struct_0(B_157)))
      | ~ v5_pre_topc(C_159,A_158,B_157)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_159,u1_struct_0(A_158),u1_struct_0(B_157))
      | ~ v1_funct_1(C_159)
      | ~ l1_pre_topc(B_157)
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_787,plain,(
    ! [A_158,C_159,D_160] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_158),u1_struct_0('#skF_4'),C_159,D_160),A_158)
      | ~ v3_pre_topc(D_160,'#skF_4')
      | ~ m1_subset_1(D_160,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v5_pre_topc(C_159,A_158,'#skF_4')
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_159,u1_struct_0(A_158),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_159)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_775])).

tff(c_801,plain,(
    ! [A_158,C_159,D_160] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_158),k2_struct_0('#skF_4'),C_159,D_160),A_158)
      | ~ v3_pre_topc(D_160,'#skF_4')
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(C_159,A_158,'#skF_4')
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_159,u1_struct_0(A_158),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_159)
      | ~ l1_pre_topc(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_89,c_89,c_89,c_787])).

tff(c_995,plain,(
    ! [A_206,C_207,D_208] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(A_206),k2_struct_0('#skF_4'),C_207,D_208),A_206)
      | ~ v3_pre_topc(D_208,'#skF_4')
      | ~ m1_subset_1(D_208,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(C_207,A_206,'#skF_4')
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_206),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_207,u1_struct_0(A_206),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_207)
      | ~ l1_pre_topc(A_206) ) ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_801])).

tff(c_999,plain,(
    ! [C_207,D_208] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0('#skF_3'),k2_struct_0('#skF_4'),C_207,D_208),'#skF_3')
      | ~ v3_pre_topc(D_208,'#skF_4')
      | ~ m1_subset_1(D_208,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(C_207,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_207,u1_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_207)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_995])).

tff(c_1009,plain,(
    ! [C_211,D_212] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),C_211,D_212),'#skF_3')
      | ~ v3_pre_topc(D_212,'#skF_4')
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(C_211,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_211,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_90,c_90,c_999])).

tff(c_1011,plain,(
    ! [D_212] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_6',D_212),'#skF_3')
      | ~ v3_pre_topc(D_212,'#skF_4')
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_168,c_1009])).

tff(c_1015,plain,(
    ! [D_213] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_6',D_213),'#skF_3')
      | ~ v3_pre_topc(D_213,'#skF_4')
      | ~ m1_subset_1(D_213,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_160,c_40,c_1011])).

tff(c_652,plain,(
    ! [B_141,A_142,C_143] :
      ( k2_struct_0(B_141) = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_142),u1_struct_0(B_141),C_143,'#skF_2'(A_142,B_141,C_143)),A_142)
      | v5_pre_topc(C_143,A_142,B_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_142),u1_struct_0(B_141))))
      | ~ v1_funct_2(C_143,u1_struct_0(A_142),u1_struct_0(B_141))
      | ~ v1_funct_1(C_143)
      | ~ l1_pre_topc(B_141)
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_658,plain,(
    ! [A_142,C_143] :
      ( k2_struct_0('#skF_5') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_142),k2_struct_0('#skF_4'),C_143,'#skF_2'(A_142,'#skF_5',C_143)),A_142)
      | v5_pre_topc(C_143,A_142,'#skF_5')
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_142),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_143,u1_struct_0(A_142),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_143)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_652])).

tff(c_674,plain,(
    ! [A_142,C_143] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_142),k2_struct_0('#skF_4'),C_143,'#skF_2'(A_142,'#skF_5',C_143)),A_142)
      | v5_pre_topc(C_143,A_142,'#skF_5')
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_142),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_143,u1_struct_0(A_142),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_143)
      | ~ l1_pre_topc(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_94,c_94,c_107,c_658])).

tff(c_882,plain,(
    ! [A_177,C_178] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_177),k2_struct_0('#skF_4'),C_178,'#skF_2'(A_177,'#skF_5',C_178)),A_177)
      | v5_pre_topc(C_178,A_177,'#skF_5')
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_178,u1_struct_0(A_177),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_178)
      | ~ l1_pre_topc(A_177) ) ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_674])).

tff(c_888,plain,(
    ! [C_178] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),C_178,'#skF_2'('#skF_3','#skF_5',C_178)),'#skF_3')
      | v5_pre_topc(C_178,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_178,u1_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_178)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_882])).

tff(c_895,plain,(
    ! [C_178] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),C_178,'#skF_2'('#skF_3','#skF_5',C_178)),'#skF_3')
      | v5_pre_topc(C_178,'#skF_3','#skF_5')
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_178,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_90,c_90,c_888])).

tff(c_1019,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1015,c_895])).

tff(c_1026,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_570,c_44,c_160,c_168,c_1019])).

tff(c_1028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1026])).

tff(c_1030,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_116,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_119,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_116])).

tff(c_126,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_119])).

tff(c_129,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_132,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_129])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_132])).

tff(c_137,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_1038,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_137])).

tff(c_1044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1038])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.56  
% 3.51/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.56  %$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.51/1.56  
% 3.51/1.56  %Foreground sorts:
% 3.51/1.56  
% 3.51/1.56  
% 3.51/1.56  %Background operators:
% 3.51/1.56  
% 3.51/1.56  
% 3.51/1.56  %Foreground operators:
% 3.51/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.51/1.56  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.51/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.51/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.51/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.51/1.56  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.51/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.51/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.51/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.51/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.51/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.51/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.51/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.51/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.51/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.56  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.51/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.51/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.51/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.51/1.56  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.51/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.51/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.56  
% 3.96/1.58  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.96/1.58  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (((u1_struct_0(B) = u1_struct_0(C)) & r1_tarski(u1_pre_topc(C), u1_pre_topc(B))) => (![D]: ((((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(C))) & v5_pre_topc(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(C)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tmap_1)).
% 3.96/1.58  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.96/1.58  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.96/1.58  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(D, B) => v3_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_2)).
% 3.96/1.58  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.96/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.96/1.58  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.96/1.58  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.96/1.58  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.58  tff(c_42, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.58  tff(c_48, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.58  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.58  tff(c_36, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_5')))) | ~v5_pre_topc('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.58  tff(c_68, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_48, c_38, c_48, c_36])).
% 3.96/1.58  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.58  tff(c_16, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.96/1.58  tff(c_74, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.96/1.58  tff(c_79, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_16, c_74])).
% 3.96/1.58  tff(c_90, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_79])).
% 3.96/1.58  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.58  tff(c_89, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_79])).
% 3.96/1.58  tff(c_93, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_42])).
% 3.96/1.58  tff(c_160, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_93])).
% 3.96/1.58  tff(c_92, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_38])).
% 3.96/1.58  tff(c_168, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_92])).
% 3.96/1.58  tff(c_50, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.58  tff(c_94, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_48])).
% 3.96/1.58  tff(c_91, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_79])).
% 3.96/1.58  tff(c_107, plain, (k2_struct_0('#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_91])).
% 3.96/1.58  tff(c_257, plain, (![A_82, B_83, C_84]: (k2_struct_0(A_82)!=k1_xboole_0 | v3_pre_topc('#skF_2'(A_82, B_83, C_84), B_83) | v5_pre_topc(C_84, A_82, B_83) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_82), u1_struct_0(B_83)))) | ~v1_funct_2(C_84, u1_struct_0(A_82), u1_struct_0(B_83)) | ~v1_funct_1(C_84) | ~l1_pre_topc(B_83) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.96/1.58  tff(c_259, plain, (![B_83, C_84]: (k2_struct_0('#skF_5')!=k1_xboole_0 | v3_pre_topc('#skF_2'('#skF_5', B_83, C_84), B_83) | v5_pre_topc(C_84, '#skF_5', B_83) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_83)))) | ~v1_funct_2(C_84, u1_struct_0('#skF_5'), u1_struct_0(B_83)) | ~v1_funct_1(C_84) | ~l1_pre_topc(B_83) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_257])).
% 3.96/1.59  tff(c_271, plain, (![B_83, C_84]: (k2_struct_0('#skF_4')!=k1_xboole_0 | v3_pre_topc('#skF_2'('#skF_5', B_83, C_84), B_83) | v5_pre_topc(C_84, '#skF_5', B_83) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_83)))) | ~v1_funct_2(C_84, k2_struct_0('#skF_4'), u1_struct_0(B_83)) | ~v1_funct_1(C_84) | ~l1_pre_topc(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_94, c_107, c_259])).
% 3.96/1.59  tff(c_289, plain, (k2_struct_0('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_271])).
% 3.96/1.59  tff(c_418, plain, (![B_108, A_109, C_110]: (k2_struct_0(B_108)=k1_xboole_0 | m1_subset_1('#skF_2'(A_109, B_108, C_110), k1_zfmisc_1(u1_struct_0(B_108))) | v5_pre_topc(C_110, A_109, B_108) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109), u1_struct_0(B_108)))) | ~v1_funct_2(C_110, u1_struct_0(A_109), u1_struct_0(B_108)) | ~v1_funct_1(C_110) | ~l1_pre_topc(B_108) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.96/1.59  tff(c_422, plain, (![A_109, C_110]: (k2_struct_0('#skF_5')=k1_xboole_0 | m1_subset_1('#skF_2'(A_109, '#skF_5', C_110), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v5_pre_topc(C_110, A_109, '#skF_5') | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_110, u1_struct_0(A_109), u1_struct_0('#skF_5')) | ~v1_funct_1(C_110) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_109))), inference(superposition, [status(thm), theory('equality')], [c_94, c_418])).
% 3.96/1.59  tff(c_434, plain, (![A_109, C_110]: (k2_struct_0('#skF_4')=k1_xboole_0 | m1_subset_1('#skF_2'(A_109, '#skF_5', C_110), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(C_110, A_109, '#skF_5') | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_110, u1_struct_0(A_109), k2_struct_0('#skF_4')) | ~v1_funct_1(C_110) | ~l1_pre_topc(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_94, c_94, c_107, c_422])).
% 3.96/1.59  tff(c_484, plain, (![A_121, C_122]: (m1_subset_1('#skF_2'(A_121, '#skF_5', C_122), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(C_122, A_121, '#skF_5') | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_121), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_122, u1_struct_0(A_121), k2_struct_0('#skF_4')) | ~v1_funct_1(C_122) | ~l1_pre_topc(A_121))), inference(negUnitSimplification, [status(thm)], [c_289, c_434])).
% 3.96/1.59  tff(c_490, plain, (![C_122]: (m1_subset_1('#skF_2'('#skF_3', '#skF_5', C_122), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(C_122, '#skF_3', '#skF_5') | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_122, u1_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_122) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_484])).
% 3.96/1.59  tff(c_526, plain, (![C_127]: (m1_subset_1('#skF_2'('#skF_3', '#skF_5', C_127), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(C_127, '#skF_3', '#skF_5') | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_127, k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_127))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_90, c_490])).
% 3.96/1.59  tff(c_529, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_2('#skF_6', k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_168, c_526])).
% 3.96/1.59  tff(c_532, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_160, c_529])).
% 3.96/1.59  tff(c_533, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_532])).
% 3.96/1.59  tff(c_46, plain, (r1_tarski(u1_pre_topc('#skF_5'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.59  tff(c_339, plain, (![B_95, A_96, C_97]: (k2_struct_0(B_95)=k1_xboole_0 | v3_pre_topc('#skF_2'(A_96, B_95, C_97), B_95) | v5_pre_topc(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96), u1_struct_0(B_95)))) | ~v1_funct_2(C_97, u1_struct_0(A_96), u1_struct_0(B_95)) | ~v1_funct_1(C_97) | ~l1_pre_topc(B_95) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.96/1.59  tff(c_343, plain, (![A_96, C_97]: (k2_struct_0('#skF_5')=k1_xboole_0 | v3_pre_topc('#skF_2'(A_96, '#skF_5', C_97), '#skF_5') | v5_pre_topc(C_97, A_96, '#skF_5') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_97, u1_struct_0(A_96), u1_struct_0('#skF_5')) | ~v1_funct_1(C_97) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_96))), inference(superposition, [status(thm), theory('equality')], [c_94, c_339])).
% 3.96/1.59  tff(c_355, plain, (![A_96, C_97]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc('#skF_2'(A_96, '#skF_5', C_97), '#skF_5') | v5_pre_topc(C_97, A_96, '#skF_5') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_96), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_97, u1_struct_0(A_96), k2_struct_0('#skF_4')) | ~v1_funct_1(C_97) | ~l1_pre_topc(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_94, c_107, c_343])).
% 3.96/1.59  tff(c_367, plain, (![A_98, C_99]: (v3_pre_topc('#skF_2'(A_98, '#skF_5', C_99), '#skF_5') | v5_pre_topc(C_99, A_98, '#skF_5') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_99, u1_struct_0(A_98), k2_struct_0('#skF_4')) | ~v1_funct_1(C_99) | ~l1_pre_topc(A_98))), inference(negUnitSimplification, [status(thm)], [c_289, c_355])).
% 3.96/1.59  tff(c_373, plain, (![C_99]: (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', C_99), '#skF_5') | v5_pre_topc(C_99, '#skF_3', '#skF_5') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_99, u1_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_99) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_367])).
% 3.96/1.59  tff(c_384, plain, (![C_101]: (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', C_101), '#skF_5') | v5_pre_topc(C_101, '#skF_3', '#skF_5') | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_101, k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_101))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_90, c_373])).
% 3.96/1.59  tff(c_387, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_5') | v5_pre_topc('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_2('#skF_6', k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_168, c_384])).
% 3.96/1.59  tff(c_390, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_5') | v5_pre_topc('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_160, c_387])).
% 3.96/1.59  tff(c_391, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_390])).
% 3.96/1.59  tff(c_200, plain, (![B_64, A_65]: (r2_hidden(B_64, u1_pre_topc(A_65)) | ~v3_pre_topc(B_64, A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.96/1.59  tff(c_203, plain, (![B_64]: (r2_hidden(B_64, u1_pre_topc('#skF_5')) | ~v3_pre_topc(B_64, '#skF_5') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_200])).
% 3.96/1.59  tff(c_211, plain, (![B_64]: (r2_hidden(B_64, u1_pre_topc('#skF_5')) | ~v3_pre_topc(B_64, '#skF_5') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_203])).
% 3.96/1.59  tff(c_539, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_5', '#skF_6'), u1_pre_topc('#skF_5')) | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_533, c_211])).
% 3.96/1.59  tff(c_549, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_5', '#skF_6'), u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_391, c_539])).
% 3.96/1.59  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.96/1.59  tff(c_556, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_3', '#skF_5', '#skF_6'), B_2) | ~r1_tarski(u1_pre_topc('#skF_5'), B_2))), inference(resolution, [status(thm)], [c_549, c_2])).
% 3.96/1.59  tff(c_209, plain, (![B_64]: (r2_hidden(B_64, u1_pre_topc('#skF_4')) | ~v3_pre_topc(B_64, '#skF_4') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_200])).
% 3.96/1.59  tff(c_215, plain, (![B_64]: (r2_hidden(B_64, u1_pre_topc('#skF_4')) | ~v3_pre_topc(B_64, '#skF_4') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_209])).
% 3.96/1.59  tff(c_546, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_5', '#skF_6'), u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_533, c_215])).
% 3.96/1.59  tff(c_553, plain, (~v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_546])).
% 3.96/1.59  tff(c_182, plain, (![B_60, A_61]: (v3_pre_topc(B_60, A_61) | ~r2_hidden(B_60, u1_pre_topc(A_61)) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.96/1.59  tff(c_191, plain, (![B_60]: (v3_pre_topc(B_60, '#skF_4') | ~r2_hidden(B_60, u1_pre_topc('#skF_4')) | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_182])).
% 3.96/1.59  tff(c_197, plain, (![B_60]: (v3_pre_topc(B_60, '#skF_4') | ~r2_hidden(B_60, u1_pre_topc('#skF_4')) | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_191])).
% 3.96/1.59  tff(c_550, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_4') | ~r2_hidden('#skF_2'('#skF_3', '#skF_5', '#skF_6'), u1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_533, c_197])).
% 3.96/1.59  tff(c_561, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_5', '#skF_6'), u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_553, c_550])).
% 3.96/1.59  tff(c_564, plain, (~r1_tarski(u1_pre_topc('#skF_5'), u1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_556, c_561])).
% 3.96/1.59  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_564])).
% 3.96/1.59  tff(c_570, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_546])).
% 3.96/1.59  tff(c_40, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.59  tff(c_775, plain, (![B_157, A_158, C_159, D_160]: (k2_struct_0(B_157)=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_158), u1_struct_0(B_157), C_159, D_160), A_158) | ~v3_pre_topc(D_160, B_157) | ~m1_subset_1(D_160, k1_zfmisc_1(u1_struct_0(B_157))) | ~v5_pre_topc(C_159, A_158, B_157) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158), u1_struct_0(B_157)))) | ~v1_funct_2(C_159, u1_struct_0(A_158), u1_struct_0(B_157)) | ~v1_funct_1(C_159) | ~l1_pre_topc(B_157) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.96/1.59  tff(c_787, plain, (![A_158, C_159, D_160]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_158), u1_struct_0('#skF_4'), C_159, D_160), A_158) | ~v3_pre_topc(D_160, '#skF_4') | ~m1_subset_1(D_160, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v5_pre_topc(C_159, A_158, '#skF_4') | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_159, u1_struct_0(A_158), u1_struct_0('#skF_4')) | ~v1_funct_1(C_159) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_158))), inference(superposition, [status(thm), theory('equality')], [c_89, c_775])).
% 3.96/1.59  tff(c_801, plain, (![A_158, C_159, D_160]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_158), k2_struct_0('#skF_4'), C_159, D_160), A_158) | ~v3_pre_topc(D_160, '#skF_4') | ~m1_subset_1(D_160, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(C_159, A_158, '#skF_4') | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_159, u1_struct_0(A_158), k2_struct_0('#skF_4')) | ~v1_funct_1(C_159) | ~l1_pre_topc(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_89, c_89, c_89, c_787])).
% 3.96/1.59  tff(c_995, plain, (![A_206, C_207, D_208]: (v3_pre_topc(k8_relset_1(u1_struct_0(A_206), k2_struct_0('#skF_4'), C_207, D_208), A_206) | ~v3_pre_topc(D_208, '#skF_4') | ~m1_subset_1(D_208, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(C_207, A_206, '#skF_4') | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_206), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_207, u1_struct_0(A_206), k2_struct_0('#skF_4')) | ~v1_funct_1(C_207) | ~l1_pre_topc(A_206))), inference(negUnitSimplification, [status(thm)], [c_289, c_801])).
% 3.96/1.59  tff(c_999, plain, (![C_207, D_208]: (v3_pre_topc(k8_relset_1(u1_struct_0('#skF_3'), k2_struct_0('#skF_4'), C_207, D_208), '#skF_3') | ~v3_pre_topc(D_208, '#skF_4') | ~m1_subset_1(D_208, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(C_207, '#skF_3', '#skF_4') | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_207, u1_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_207) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_995])).
% 3.96/1.59  tff(c_1009, plain, (![C_211, D_212]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), C_211, D_212), '#skF_3') | ~v3_pre_topc(D_212, '#skF_4') | ~m1_subset_1(D_212, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(C_211, '#skF_3', '#skF_4') | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_211, k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_211))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_90, c_90, c_999])).
% 3.96/1.59  tff(c_1011, plain, (![D_212]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_6', D_212), '#skF_3') | ~v3_pre_topc(D_212, '#skF_4') | ~m1_subset_1(D_212, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_6', k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_168, c_1009])).
% 3.96/1.59  tff(c_1015, plain, (![D_213]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_6', D_213), '#skF_3') | ~v3_pre_topc(D_213, '#skF_4') | ~m1_subset_1(D_213, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_160, c_40, c_1011])).
% 3.96/1.59  tff(c_652, plain, (![B_141, A_142, C_143]: (k2_struct_0(B_141)=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_142), u1_struct_0(B_141), C_143, '#skF_2'(A_142, B_141, C_143)), A_142) | v5_pre_topc(C_143, A_142, B_141) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_142), u1_struct_0(B_141)))) | ~v1_funct_2(C_143, u1_struct_0(A_142), u1_struct_0(B_141)) | ~v1_funct_1(C_143) | ~l1_pre_topc(B_141) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.96/1.59  tff(c_658, plain, (![A_142, C_143]: (k2_struct_0('#skF_5')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_142), k2_struct_0('#skF_4'), C_143, '#skF_2'(A_142, '#skF_5', C_143)), A_142) | v5_pre_topc(C_143, A_142, '#skF_5') | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_142), u1_struct_0('#skF_5')))) | ~v1_funct_2(C_143, u1_struct_0(A_142), u1_struct_0('#skF_5')) | ~v1_funct_1(C_143) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_142))), inference(superposition, [status(thm), theory('equality')], [c_94, c_652])).
% 3.96/1.59  tff(c_674, plain, (![A_142, C_143]: (k2_struct_0('#skF_4')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_142), k2_struct_0('#skF_4'), C_143, '#skF_2'(A_142, '#skF_5', C_143)), A_142) | v5_pre_topc(C_143, A_142, '#skF_5') | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_142), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_143, u1_struct_0(A_142), k2_struct_0('#skF_4')) | ~v1_funct_1(C_143) | ~l1_pre_topc(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_94, c_94, c_107, c_658])).
% 3.96/1.59  tff(c_882, plain, (![A_177, C_178]: (~v3_pre_topc(k8_relset_1(u1_struct_0(A_177), k2_struct_0('#skF_4'), C_178, '#skF_2'(A_177, '#skF_5', C_178)), A_177) | v5_pre_topc(C_178, A_177, '#skF_5') | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_178, u1_struct_0(A_177), k2_struct_0('#skF_4')) | ~v1_funct_1(C_178) | ~l1_pre_topc(A_177))), inference(negUnitSimplification, [status(thm)], [c_289, c_674])).
% 3.96/1.59  tff(c_888, plain, (![C_178]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), C_178, '#skF_2'('#skF_3', '#skF_5', C_178)), '#skF_3') | v5_pre_topc(C_178, '#skF_3', '#skF_5') | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_178, u1_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_178) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_882])).
% 3.96/1.59  tff(c_895, plain, (![C_178]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), C_178, '#skF_2'('#skF_3', '#skF_5', C_178)), '#skF_3') | v5_pre_topc(C_178, '#skF_3', '#skF_5') | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_178, k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_178))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_90, c_90, c_888])).
% 3.96/1.59  tff(c_1019, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_5', '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1015, c_895])).
% 3.96/1.59  tff(c_1026, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_570, c_44, c_160, c_168, c_1019])).
% 3.96/1.59  tff(c_1028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1026])).
% 3.96/1.59  tff(c_1030, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_271])).
% 3.96/1.59  tff(c_54, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.96/1.59  tff(c_116, plain, (![A_48]: (~v1_xboole_0(u1_struct_0(A_48)) | ~l1_struct_0(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.96/1.59  tff(c_119, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_94, c_116])).
% 3.96/1.59  tff(c_126, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_119])).
% 3.96/1.59  tff(c_129, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_126])).
% 3.96/1.59  tff(c_132, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_129])).
% 3.96/1.59  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_132])).
% 3.96/1.59  tff(c_137, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_126])).
% 3.96/1.59  tff(c_1038, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_137])).
% 3.96/1.59  tff(c_1044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1038])).
% 3.96/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.59  
% 3.96/1.59  Inference rules
% 3.96/1.59  ----------------------
% 3.96/1.59  #Ref     : 0
% 3.96/1.59  #Sup     : 186
% 3.96/1.59  #Fact    : 0
% 3.96/1.59  #Define  : 0
% 3.96/1.59  #Split   : 6
% 3.96/1.59  #Chain   : 0
% 3.96/1.59  #Close   : 0
% 3.96/1.59  
% 3.96/1.59  Ordering : KBO
% 3.96/1.59  
% 3.96/1.59  Simplification rules
% 3.96/1.59  ----------------------
% 3.96/1.59  #Subsume      : 63
% 3.96/1.59  #Demod        : 394
% 3.96/1.59  #Tautology    : 22
% 3.96/1.59  #SimpNegUnit  : 46
% 3.96/1.59  #BackRed      : 14
% 3.96/1.59  
% 3.96/1.59  #Partial instantiations: 0
% 3.96/1.59  #Strategies tried      : 1
% 3.96/1.59  
% 3.96/1.59  Timing (in seconds)
% 3.96/1.59  ----------------------
% 3.96/1.59  Preprocessing        : 0.32
% 3.96/1.59  Parsing              : 0.17
% 3.96/1.59  CNF conversion       : 0.03
% 3.96/1.59  Main loop            : 0.53
% 3.96/1.59  Inferencing          : 0.18
% 3.96/1.59  Reduction            : 0.19
% 3.96/1.59  Demodulation         : 0.14
% 3.96/1.59  BG Simplification    : 0.02
% 3.96/1.59  Subsumption          : 0.10
% 3.96/1.59  Abstraction          : 0.02
% 3.96/1.59  MUC search           : 0.00
% 3.96/1.59  Cooper               : 0.00
% 3.96/1.59  Total                : 0.90
% 3.96/1.59  Index Insertion      : 0.00
% 3.96/1.59  Index Deletion       : 0.00
% 3.96/1.59  Index Matching       : 0.00
% 3.96/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
