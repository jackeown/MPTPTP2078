%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:49 EST 2020

% Result     : Theorem 5.61s
% Output     : CNFRefutation 5.61s
% Verified   : 
% Statistics : Number of formulae       :  136 (1751 expanded)
%              Number of leaves         :   36 ( 628 expanded)
%              Depth                    :   20
%              Number of atoms          :  379 (8712 expanded)
%              Number of equality atoms :   29 (1062 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tmap_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_87,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_67,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_4'))))
    | ~ v5_pre_topc('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_2'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_70,plain,(
    ~ v5_pre_topc('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_67,c_68,c_36])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_16,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_93,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_91,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_81])).

tff(c_94,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_2'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_67])).

tff(c_117,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_2'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_94])).

tff(c_173,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_93,c_68])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_99,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_48])).

tff(c_92,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_81])).

tff(c_108,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_92])).

tff(c_276,plain,(
    ! [B_72,A_73,C_74] :
      ( k2_struct_0(B_72) = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_73,B_72,C_74),B_72)
      | v5_pre_topc(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73),u1_struct_0(B_72))))
      | ~ v1_funct_2(C_74,u1_struct_0(A_73),u1_struct_0(B_72))
      | ~ v1_funct_1(C_74)
      | ~ l1_pre_topc(B_72)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_283,plain,(
    ! [A_73,C_74] :
      ( k2_struct_0('#skF_3') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_73,'#skF_3',C_74),'#skF_3')
      | v5_pre_topc(C_74,A_73,'#skF_3')
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_74,u1_struct_0(A_73),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_74)
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_276])).

tff(c_296,plain,(
    ! [A_73,C_74] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_73,'#skF_3',C_74),'#skF_3')
      | v5_pre_topc(C_74,A_73,'#skF_3')
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_74,u1_struct_0(A_73),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_74)
      | ~ l1_pre_topc(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_99,c_108,c_283])).

tff(c_361,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_124,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(u1_struct_0(A_53))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_127,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_124])).

tff(c_134,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_127])).

tff(c_137,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_141,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_137])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_141])).

tff(c_146,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_372,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_146])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_372])).

tff(c_381,plain,(
    k2_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_475,plain,(
    ! [B_104,A_105,C_106] :
      ( k2_struct_0(B_104) = k1_xboole_0
      | m1_subset_1('#skF_1'(A_105,B_104,C_106),k1_zfmisc_1(u1_struct_0(B_104)))
      | v5_pre_topc(C_106,A_105,B_104)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_106,u1_struct_0(A_105),u1_struct_0(B_104))
      | ~ v1_funct_1(C_106)
      | ~ l1_pre_topc(B_104)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_486,plain,(
    ! [A_105,C_106] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | m1_subset_1('#skF_1'(A_105,'#skF_4',C_106),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v5_pre_topc(C_106,A_105,'#skF_4')
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_106,u1_struct_0(A_105),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_106)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_475])).

tff(c_500,plain,(
    ! [A_105,C_106] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | m1_subset_1('#skF_1'(A_105,'#skF_4',C_106),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(C_106,A_105,'#skF_4')
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_106,u1_struct_0(A_105),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_106)
      | ~ l1_pre_topc(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_93,c_93,c_486])).

tff(c_550,plain,(
    ! [A_114,C_115] :
      ( m1_subset_1('#skF_1'(A_114,'#skF_4',C_115),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(C_115,A_114,'#skF_4')
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_114),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_115,u1_struct_0(A_114),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_115)
      | ~ l1_pre_topc(A_114) ) ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_500])).

tff(c_563,plain,(
    ! [C_115] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_4',C_115),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(C_115,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_115,u1_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_115)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_550])).

tff(c_614,plain,(
    ! [C_123] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_4',C_123),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(C_123,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_123,k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91,c_563])).

tff(c_617,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v5_pre_topc('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_173,c_614])).

tff(c_624,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v5_pre_topc('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_117,c_617])).

tff(c_625,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_624])).

tff(c_207,plain,(
    ! [B_61,A_62] :
      ( r2_hidden(B_61,u1_pre_topc(A_62))
      | ~ v3_pre_topc(B_61,A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_214,plain,(
    ! [B_61] :
      ( r2_hidden(B_61,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_61,'#skF_3')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_207])).

tff(c_223,plain,(
    ! [B_61] :
      ( r2_hidden(B_61,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(B_61,'#skF_3')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_214])).

tff(c_642,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_5'),u1_pre_topc('#skF_3'))
    | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_625,c_223])).

tff(c_653,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_642])).

tff(c_46,plain,(
    r1_tarski(u1_pre_topc('#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_646,plain,(
    r1_tarski('#skF_1'('#skF_2','#skF_4','#skF_5'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_625,c_6])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_217,plain,(
    ! [B_61] :
      ( r2_hidden(B_61,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(B_61,'#skF_4')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_207])).

tff(c_225,plain,(
    ! [B_61] :
      ( r2_hidden(B_61,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(B_61,'#skF_4')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_217])).

tff(c_643,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_5'),u1_pre_topc('#skF_4'))
    | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_625,c_225])).

tff(c_654,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_177,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_173,c_6])).

tff(c_1081,plain,(
    ! [B_179,A_180,A_181] :
      ( k2_struct_0(B_179) = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_180,B_179,A_181),B_179)
      | v5_pre_topc(A_181,A_180,B_179)
      | ~ v1_funct_2(A_181,u1_struct_0(A_180),u1_struct_0(B_179))
      | ~ v1_funct_1(A_181)
      | ~ l1_pre_topc(B_179)
      | ~ l1_pre_topc(A_180)
      | ~ r1_tarski(A_181,k2_zfmisc_1(u1_struct_0(A_180),u1_struct_0(B_179))) ) ),
    inference(resolution,[status(thm)],[c_8,c_276])).

tff(c_1089,plain,(
    ! [A_180,A_181] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_180,'#skF_4',A_181),'#skF_4')
      | v5_pre_topc(A_181,A_180,'#skF_4')
      | ~ v1_funct_2(A_181,u1_struct_0(A_180),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(A_181)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_180)
      | ~ r1_tarski(A_181,k2_zfmisc_1(u1_struct_0(A_180),k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_1081])).

tff(c_1102,plain,(
    ! [A_180,A_181] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc('#skF_1'(A_180,'#skF_4',A_181),'#skF_4')
      | v5_pre_topc(A_181,A_180,'#skF_4')
      | ~ v1_funct_2(A_181,u1_struct_0(A_180),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_181)
      | ~ l1_pre_topc(A_180)
      | ~ r1_tarski(A_181,k2_zfmisc_1(u1_struct_0(A_180),k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_93,c_1089])).

tff(c_1116,plain,(
    ! [A_184,A_185] :
      ( v3_pre_topc('#skF_1'(A_184,'#skF_4',A_185),'#skF_4')
      | v5_pre_topc(A_185,A_184,'#skF_4')
      | ~ v1_funct_2(A_185,u1_struct_0(A_184),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_185)
      | ~ l1_pre_topc(A_184)
      | ~ r1_tarski(A_185,k2_zfmisc_1(u1_struct_0(A_184),k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_1102])).

tff(c_1125,plain,(
    ! [A_185] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_4',A_185),'#skF_4')
      | v5_pre_topc(A_185,'#skF_2','#skF_4')
      | ~ v1_funct_2(A_185,u1_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_185)
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_185,k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_1116])).

tff(c_1132,plain,(
    ! [A_186] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_4',A_186),'#skF_4')
      | v5_pre_topc(A_186,'#skF_2','#skF_4')
      | ~ v1_funct_2(A_186,k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(A_186)
      | ~ r1_tarski(A_186,k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91,c_1125])).

tff(c_1135,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_4')
    | v5_pre_topc('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_177,c_1132])).

tff(c_1138,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_4')
    | v5_pre_topc('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_117,c_1135])).

tff(c_1140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_654,c_1138])).

tff(c_1141,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_4,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1158,plain,(
    ! [A_187] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_5'),A_187)
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(A_187)) ) ),
    inference(resolution,[status(thm)],[c_1141,c_4])).

tff(c_1164,plain,(
    ! [B_188] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_5'),B_188)
      | ~ r1_tarski(u1_pre_topc('#skF_4'),B_188) ) ),
    inference(resolution,[status(thm)],[c_8,c_1158])).

tff(c_179,plain,(
    ! [B_57,A_58] :
      ( v3_pre_topc(B_57,A_58)
      | ~ r2_hidden(B_57,u1_pre_topc(A_58))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_186,plain,(
    ! [B_57] :
      ( v3_pre_topc(B_57,'#skF_3')
      | ~ r2_hidden(B_57,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_179])).

tff(c_200,plain,(
    ! [B_59] :
      ( v3_pre_topc(B_59,'#skF_3')
      | ~ r2_hidden(B_59,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_186])).

tff(c_205,plain,(
    ! [A_5] :
      ( v3_pre_topc(A_5,'#skF_3')
      | ~ r2_hidden(A_5,u1_pre_topc('#skF_3'))
      | ~ r1_tarski(A_5,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8,c_200])).

tff(c_1180,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ r1_tarski('#skF_1'('#skF_2','#skF_4','#skF_5'),k2_struct_0('#skF_4'))
    | ~ r1_tarski(u1_pre_topc('#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1164,c_205])).

tff(c_1190,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_646,c_1180])).

tff(c_1192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_653,c_1190])).

tff(c_1194,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_642])).

tff(c_40,plain,(
    v5_pre_topc('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1699,plain,(
    ! [B_248,A_249,C_250,D_251] :
      ( k2_struct_0(B_248) = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_249),u1_struct_0(B_248),C_250,D_251),A_249)
      | ~ v3_pre_topc(D_251,B_248)
      | ~ m1_subset_1(D_251,k1_zfmisc_1(u1_struct_0(B_248)))
      | ~ v5_pre_topc(C_250,A_249,B_248)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),u1_struct_0(B_248))))
      | ~ v1_funct_2(C_250,u1_struct_0(A_249),u1_struct_0(B_248))
      | ~ v1_funct_1(C_250)
      | ~ l1_pre_topc(B_248)
      | ~ l1_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1706,plain,(
    ! [A_249,C_250,D_251] :
      ( k2_struct_0('#skF_3') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_249),u1_struct_0('#skF_3'),C_250,D_251),A_249)
      | ~ v3_pre_topc(D_251,'#skF_3')
      | ~ m1_subset_1(D_251,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc(C_250,A_249,'#skF_3')
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_250,u1_struct_0(A_249),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_250)
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_249) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_1699])).

tff(c_1719,plain,(
    ! [A_249,C_250,D_251] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | v3_pre_topc(k8_relset_1(u1_struct_0(A_249),k2_struct_0('#skF_4'),C_250,D_251),A_249)
      | ~ v3_pre_topc(D_251,'#skF_3')
      | ~ m1_subset_1(D_251,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(C_250,A_249,'#skF_3')
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_250,u1_struct_0(A_249),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_250)
      | ~ l1_pre_topc(A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_99,c_99,c_99,c_108,c_1706])).

tff(c_2836,plain,(
    ! [A_404,C_405,D_406] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(A_404),k2_struct_0('#skF_4'),C_405,D_406),A_404)
      | ~ v3_pre_topc(D_406,'#skF_3')
      | ~ m1_subset_1(D_406,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(C_405,A_404,'#skF_3')
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_405,u1_struct_0(A_404),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_405)
      | ~ l1_pre_topc(A_404) ) ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_1719])).

tff(c_2845,plain,(
    ! [C_405,D_406] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_4'),C_405,D_406),'#skF_2')
      | ~ v3_pre_topc(D_406,'#skF_3')
      | ~ m1_subset_1(D_406,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(C_405,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_405,u1_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_405)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2836])).

tff(c_2880,plain,(
    ! [C_414,D_415] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'),C_414,D_415),'#skF_2')
      | ~ v3_pre_topc(D_415,'#skF_3')
      | ~ m1_subset_1(D_415,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc(C_414,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_414,k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_414) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91,c_91,c_2845])).

tff(c_2882,plain,(
    ! [D_415] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'),'#skF_5',D_415),'#skF_2')
      | ~ v3_pre_topc(D_415,'#skF_3')
      | ~ m1_subset_1(D_415,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v5_pre_topc('#skF_5','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_173,c_2880])).

tff(c_2890,plain,(
    ! [D_416] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'),'#skF_5',D_416),'#skF_2')
      | ~ v3_pre_topc(D_416,'#skF_3')
      | ~ m1_subset_1(D_416,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_117,c_40,c_2882])).

tff(c_1195,plain,(
    ! [B_189,A_190,C_191] :
      ( k2_struct_0(B_189) = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_190),u1_struct_0(B_189),C_191,'#skF_1'(A_190,B_189,C_191)),A_190)
      | v5_pre_topc(C_191,A_190,B_189)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190),u1_struct_0(B_189))))
      | ~ v1_funct_2(C_191,u1_struct_0(A_190),u1_struct_0(B_189))
      | ~ v1_funct_1(C_191)
      | ~ l1_pre_topc(B_189)
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1207,plain,(
    ! [A_190,C_191] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_190),k2_struct_0('#skF_4'),C_191,'#skF_1'(A_190,'#skF_4',C_191)),A_190)
      | v5_pre_topc(C_191,A_190,'#skF_4')
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_191,u1_struct_0(A_190),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_191)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_1195])).

tff(c_1222,plain,(
    ! [A_190,C_191] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_190),k2_struct_0('#skF_4'),C_191,'#skF_1'(A_190,'#skF_4',C_191)),A_190)
      | v5_pre_topc(C_191,A_190,'#skF_4')
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_191,u1_struct_0(A_190),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_191)
      | ~ l1_pre_topc(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_93,c_93,c_1207])).

tff(c_2560,plain,(
    ! [A_358,C_359] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_358),k2_struct_0('#skF_4'),C_359,'#skF_1'(A_358,'#skF_4',C_359)),A_358)
      | v5_pre_topc(C_359,A_358,'#skF_4')
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_358),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_359,u1_struct_0(A_358),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_359)
      | ~ l1_pre_topc(A_358) ) ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_1222])).

tff(c_2569,plain,(
    ! [C_359] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'),C_359,'#skF_1'('#skF_2','#skF_4',C_359)),'#skF_2')
      | v5_pre_topc(C_359,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_359,u1_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_359)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2560])).

tff(c_2575,plain,(
    ! [C_359] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'),C_359,'#skF_1'('#skF_2','#skF_4',C_359)),'#skF_2')
      | v5_pre_topc(C_359,'#skF_2','#skF_4')
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_359,k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91,c_91,c_2569])).

tff(c_2894,plain,
    ( v5_pre_topc('#skF_5','#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_2'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_4','#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_2890,c_2575])).

tff(c_2901,plain,(
    v5_pre_topc('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_1194,c_44,c_117,c_173,c_2894])).

tff(c_2903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2901])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.61/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.61/2.01  
% 5.61/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.61/2.01  %$ v5_pre_topc > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.61/2.01  
% 5.61/2.01  %Foreground sorts:
% 5.61/2.01  
% 5.61/2.01  
% 5.61/2.01  %Background operators:
% 5.61/2.01  
% 5.61/2.01  
% 5.61/2.01  %Foreground operators:
% 5.61/2.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.61/2.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.61/2.01  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.61/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.61/2.01  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.61/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.61/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.61/2.01  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.61/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.61/2.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.61/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.61/2.01  tff('#skF_5', type, '#skF_5': $i).
% 5.61/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.61/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.61/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.61/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.61/2.01  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.61/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.61/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.61/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.61/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.61/2.01  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.61/2.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.61/2.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.61/2.01  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.61/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.61/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.61/2.01  
% 5.61/2.04  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (((u1_struct_0(B) = u1_struct_0(C)) & r1_tarski(u1_pre_topc(C), u1_pre_topc(B))) => (![D]: ((((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(C))) & v5_pre_topc(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(C)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tmap_1)).
% 5.61/2.04  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.61/2.04  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.61/2.04  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.61/2.04  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(D, B) => v3_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_2)).
% 5.61/2.04  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.61/2.04  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 5.61/2.04  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.61/2.04  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.61/2.04  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_48, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_42, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_67, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42])).
% 5.61/2.04  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38])).
% 5.61/2.04  tff(c_36, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_4')))) | ~v5_pre_topc('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_2'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_70, plain, (~v5_pre_topc('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_67, c_68, c_36])).
% 5.61/2.04  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_16, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.61/2.04  tff(c_76, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.61/2.04  tff(c_81, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_pre_topc(A_48))), inference(resolution, [status(thm)], [c_16, c_76])).
% 5.61/2.04  tff(c_93, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_81])).
% 5.61/2.04  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_91, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_81])).
% 5.61/2.04  tff(c_94, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_2'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_67])).
% 5.61/2.04  tff(c_117, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_2'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_94])).
% 5.61/2.04  tff(c_173, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_93, c_68])).
% 5.61/2.04  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.61/2.04  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_99, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_48])).
% 5.61/2.04  tff(c_92, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_56, c_81])).
% 5.61/2.04  tff(c_108, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_92])).
% 5.61/2.04  tff(c_276, plain, (![B_72, A_73, C_74]: (k2_struct_0(B_72)=k1_xboole_0 | v3_pre_topc('#skF_1'(A_73, B_72, C_74), B_72) | v5_pre_topc(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73), u1_struct_0(B_72)))) | ~v1_funct_2(C_74, u1_struct_0(A_73), u1_struct_0(B_72)) | ~v1_funct_1(C_74) | ~l1_pre_topc(B_72) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.61/2.04  tff(c_283, plain, (![A_73, C_74]: (k2_struct_0('#skF_3')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_73, '#skF_3', C_74), '#skF_3') | v5_pre_topc(C_74, A_73, '#skF_3') | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_74, u1_struct_0(A_73), u1_struct_0('#skF_3')) | ~v1_funct_1(C_74) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_73))), inference(superposition, [status(thm), theory('equality')], [c_99, c_276])).
% 5.61/2.04  tff(c_296, plain, (![A_73, C_74]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_73, '#skF_3', C_74), '#skF_3') | v5_pre_topc(C_74, A_73, '#skF_3') | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_74, u1_struct_0(A_73), k2_struct_0('#skF_4')) | ~v1_funct_1(C_74) | ~l1_pre_topc(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_99, c_108, c_283])).
% 5.61/2.04  tff(c_361, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_296])).
% 5.61/2.04  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_124, plain, (![A_53]: (~v1_xboole_0(u1_struct_0(A_53)) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.61/2.04  tff(c_127, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_99, c_124])).
% 5.61/2.04  tff(c_134, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_127])).
% 5.61/2.04  tff(c_137, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_134])).
% 5.61/2.04  tff(c_141, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_137])).
% 5.61/2.04  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_141])).
% 5.61/2.04  tff(c_146, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_134])).
% 5.61/2.04  tff(c_372, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_361, c_146])).
% 5.61/2.04  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_372])).
% 5.61/2.04  tff(c_381, plain, (k2_struct_0('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_296])).
% 5.61/2.04  tff(c_475, plain, (![B_104, A_105, C_106]: (k2_struct_0(B_104)=k1_xboole_0 | m1_subset_1('#skF_1'(A_105, B_104, C_106), k1_zfmisc_1(u1_struct_0(B_104))) | v5_pre_topc(C_106, A_105, B_104) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105), u1_struct_0(B_104)))) | ~v1_funct_2(C_106, u1_struct_0(A_105), u1_struct_0(B_104)) | ~v1_funct_1(C_106) | ~l1_pre_topc(B_104) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.61/2.04  tff(c_486, plain, (![A_105, C_106]: (k2_struct_0('#skF_4')=k1_xboole_0 | m1_subset_1('#skF_1'(A_105, '#skF_4', C_106), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v5_pre_topc(C_106, A_105, '#skF_4') | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_106, u1_struct_0(A_105), u1_struct_0('#skF_4')) | ~v1_funct_1(C_106) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_105))), inference(superposition, [status(thm), theory('equality')], [c_93, c_475])).
% 5.61/2.04  tff(c_500, plain, (![A_105, C_106]: (k2_struct_0('#skF_4')=k1_xboole_0 | m1_subset_1('#skF_1'(A_105, '#skF_4', C_106), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(C_106, A_105, '#skF_4') | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_106, u1_struct_0(A_105), k2_struct_0('#skF_4')) | ~v1_funct_1(C_106) | ~l1_pre_topc(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_93, c_93, c_486])).
% 5.61/2.04  tff(c_550, plain, (![A_114, C_115]: (m1_subset_1('#skF_1'(A_114, '#skF_4', C_115), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(C_115, A_114, '#skF_4') | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_114), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_115, u1_struct_0(A_114), k2_struct_0('#skF_4')) | ~v1_funct_1(C_115) | ~l1_pre_topc(A_114))), inference(negUnitSimplification, [status(thm)], [c_381, c_500])).
% 5.61/2.04  tff(c_563, plain, (![C_115]: (m1_subset_1('#skF_1'('#skF_2', '#skF_4', C_115), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(C_115, '#skF_2', '#skF_4') | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_115, u1_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_115) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_550])).
% 5.61/2.04  tff(c_614, plain, (![C_123]: (m1_subset_1('#skF_1'('#skF_2', '#skF_4', C_123), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc(C_123, '#skF_2', '#skF_4') | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_123, k2_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_123))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91, c_563])).
% 5.61/2.04  tff(c_617, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_173, c_614])).
% 5.61/2.04  tff(c_624, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v5_pre_topc('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_117, c_617])).
% 5.61/2.04  tff(c_625, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_624])).
% 5.61/2.04  tff(c_207, plain, (![B_61, A_62]: (r2_hidden(B_61, u1_pre_topc(A_62)) | ~v3_pre_topc(B_61, A_62) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.61/2.04  tff(c_214, plain, (![B_61]: (r2_hidden(B_61, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_61, '#skF_3') | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_207])).
% 5.61/2.04  tff(c_223, plain, (![B_61]: (r2_hidden(B_61, u1_pre_topc('#skF_3')) | ~v3_pre_topc(B_61, '#skF_3') | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_214])).
% 5.61/2.04  tff(c_642, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_5'), u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_625, c_223])).
% 5.61/2.04  tff(c_653, plain, (~v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_642])).
% 5.61/2.04  tff(c_46, plain, (r1_tarski(u1_pre_topc('#skF_4'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.61/2.04  tff(c_646, plain, (r1_tarski('#skF_1'('#skF_2', '#skF_4', '#skF_5'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_625, c_6])).
% 5.61/2.04  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.61/2.04  tff(c_217, plain, (![B_61]: (r2_hidden(B_61, u1_pre_topc('#skF_4')) | ~v3_pre_topc(B_61, '#skF_4') | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_207])).
% 5.61/2.04  tff(c_225, plain, (![B_61]: (r2_hidden(B_61, u1_pre_topc('#skF_4')) | ~v3_pre_topc(B_61, '#skF_4') | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_217])).
% 5.61/2.04  tff(c_643, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_5'), u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_625, c_225])).
% 5.61/2.04  tff(c_654, plain, (~v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_643])).
% 5.61/2.04  tff(c_177, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_173, c_6])).
% 5.61/2.04  tff(c_1081, plain, (![B_179, A_180, A_181]: (k2_struct_0(B_179)=k1_xboole_0 | v3_pre_topc('#skF_1'(A_180, B_179, A_181), B_179) | v5_pre_topc(A_181, A_180, B_179) | ~v1_funct_2(A_181, u1_struct_0(A_180), u1_struct_0(B_179)) | ~v1_funct_1(A_181) | ~l1_pre_topc(B_179) | ~l1_pre_topc(A_180) | ~r1_tarski(A_181, k2_zfmisc_1(u1_struct_0(A_180), u1_struct_0(B_179))))), inference(resolution, [status(thm)], [c_8, c_276])).
% 5.61/2.04  tff(c_1089, plain, (![A_180, A_181]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_180, '#skF_4', A_181), '#skF_4') | v5_pre_topc(A_181, A_180, '#skF_4') | ~v1_funct_2(A_181, u1_struct_0(A_180), u1_struct_0('#skF_4')) | ~v1_funct_1(A_181) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_180) | ~r1_tarski(A_181, k2_zfmisc_1(u1_struct_0(A_180), k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_93, c_1081])).
% 5.61/2.04  tff(c_1102, plain, (![A_180, A_181]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc('#skF_1'(A_180, '#skF_4', A_181), '#skF_4') | v5_pre_topc(A_181, A_180, '#skF_4') | ~v1_funct_2(A_181, u1_struct_0(A_180), k2_struct_0('#skF_4')) | ~v1_funct_1(A_181) | ~l1_pre_topc(A_180) | ~r1_tarski(A_181, k2_zfmisc_1(u1_struct_0(A_180), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_93, c_1089])).
% 5.61/2.04  tff(c_1116, plain, (![A_184, A_185]: (v3_pre_topc('#skF_1'(A_184, '#skF_4', A_185), '#skF_4') | v5_pre_topc(A_185, A_184, '#skF_4') | ~v1_funct_2(A_185, u1_struct_0(A_184), k2_struct_0('#skF_4')) | ~v1_funct_1(A_185) | ~l1_pre_topc(A_184) | ~r1_tarski(A_185, k2_zfmisc_1(u1_struct_0(A_184), k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_381, c_1102])).
% 5.61/2.04  tff(c_1125, plain, (![A_185]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', A_185), '#skF_4') | v5_pre_topc(A_185, '#skF_2', '#skF_4') | ~v1_funct_2(A_185, u1_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(A_185) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_185, k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_91, c_1116])).
% 5.61/2.04  tff(c_1132, plain, (![A_186]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', A_186), '#skF_4') | v5_pre_topc(A_186, '#skF_2', '#skF_4') | ~v1_funct_2(A_186, k2_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(A_186) | ~r1_tarski(A_186, k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91, c_1125])).
% 5.61/2.04  tff(c_1135, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_4') | v5_pre_topc('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_177, c_1132])).
% 5.61/2.04  tff(c_1138, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_4') | v5_pre_topc('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_117, c_1135])).
% 5.61/2.04  tff(c_1140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_654, c_1138])).
% 5.61/2.04  tff(c_1141, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_5'), u1_pre_topc('#skF_4'))), inference(splitRight, [status(thm)], [c_643])).
% 5.61/2.04  tff(c_4, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.61/2.04  tff(c_1158, plain, (![A_187]: (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_5'), A_187) | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(A_187)))), inference(resolution, [status(thm)], [c_1141, c_4])).
% 5.61/2.04  tff(c_1164, plain, (![B_188]: (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_5'), B_188) | ~r1_tarski(u1_pre_topc('#skF_4'), B_188))), inference(resolution, [status(thm)], [c_8, c_1158])).
% 5.61/2.04  tff(c_179, plain, (![B_57, A_58]: (v3_pre_topc(B_57, A_58) | ~r2_hidden(B_57, u1_pre_topc(A_58)) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.61/2.04  tff(c_186, plain, (![B_57]: (v3_pre_topc(B_57, '#skF_3') | ~r2_hidden(B_57, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_179])).
% 5.61/2.04  tff(c_200, plain, (![B_59]: (v3_pre_topc(B_59, '#skF_3') | ~r2_hidden(B_59, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_186])).
% 5.61/2.04  tff(c_205, plain, (![A_5]: (v3_pre_topc(A_5, '#skF_3') | ~r2_hidden(A_5, u1_pre_topc('#skF_3')) | ~r1_tarski(A_5, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_8, c_200])).
% 5.61/2.04  tff(c_1180, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~r1_tarski('#skF_1'('#skF_2', '#skF_4', '#skF_5'), k2_struct_0('#skF_4')) | ~r1_tarski(u1_pre_topc('#skF_4'), u1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_1164, c_205])).
% 5.61/2.04  tff(c_1190, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_646, c_1180])).
% 5.61/2.04  tff(c_1192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_653, c_1190])).
% 5.61/2.04  tff(c_1194, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_642])).
% 5.61/2.04  tff(c_40, plain, (v5_pre_topc('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.61/2.04  tff(c_1699, plain, (![B_248, A_249, C_250, D_251]: (k2_struct_0(B_248)=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_249), u1_struct_0(B_248), C_250, D_251), A_249) | ~v3_pre_topc(D_251, B_248) | ~m1_subset_1(D_251, k1_zfmisc_1(u1_struct_0(B_248))) | ~v5_pre_topc(C_250, A_249, B_248) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), u1_struct_0(B_248)))) | ~v1_funct_2(C_250, u1_struct_0(A_249), u1_struct_0(B_248)) | ~v1_funct_1(C_250) | ~l1_pre_topc(B_248) | ~l1_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.61/2.04  tff(c_1706, plain, (![A_249, C_250, D_251]: (k2_struct_0('#skF_3')=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_249), u1_struct_0('#skF_3'), C_250, D_251), A_249) | ~v3_pre_topc(D_251, '#skF_3') | ~m1_subset_1(D_251, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v5_pre_topc(C_250, A_249, '#skF_3') | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_250, u1_struct_0(A_249), u1_struct_0('#skF_3')) | ~v1_funct_1(C_250) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_249))), inference(superposition, [status(thm), theory('equality')], [c_99, c_1699])).
% 5.61/2.04  tff(c_1719, plain, (![A_249, C_250, D_251]: (k2_struct_0('#skF_4')=k1_xboole_0 | v3_pre_topc(k8_relset_1(u1_struct_0(A_249), k2_struct_0('#skF_4'), C_250, D_251), A_249) | ~v3_pre_topc(D_251, '#skF_3') | ~m1_subset_1(D_251, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(C_250, A_249, '#skF_3') | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_250, u1_struct_0(A_249), k2_struct_0('#skF_4')) | ~v1_funct_1(C_250) | ~l1_pre_topc(A_249))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_99, c_99, c_99, c_108, c_1706])).
% 5.61/2.04  tff(c_2836, plain, (![A_404, C_405, D_406]: (v3_pre_topc(k8_relset_1(u1_struct_0(A_404), k2_struct_0('#skF_4'), C_405, D_406), A_404) | ~v3_pre_topc(D_406, '#skF_3') | ~m1_subset_1(D_406, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(C_405, A_404, '#skF_3') | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_405, u1_struct_0(A_404), k2_struct_0('#skF_4')) | ~v1_funct_1(C_405) | ~l1_pre_topc(A_404))), inference(negUnitSimplification, [status(thm)], [c_381, c_1719])).
% 5.61/2.04  tff(c_2845, plain, (![C_405, D_406]: (v3_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_4'), C_405, D_406), '#skF_2') | ~v3_pre_topc(D_406, '#skF_3') | ~m1_subset_1(D_406, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(C_405, '#skF_2', '#skF_3') | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_405, u1_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_405) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_2836])).
% 5.61/2.04  tff(c_2880, plain, (![C_414, D_415]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4'), C_414, D_415), '#skF_2') | ~v3_pre_topc(D_415, '#skF_3') | ~m1_subset_1(D_415, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc(C_414, '#skF_2', '#skF_3') | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_414, k2_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_414))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91, c_91, c_2845])).
% 5.61/2.04  tff(c_2882, plain, (![D_415]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4'), '#skF_5', D_415), '#skF_2') | ~v3_pre_topc(D_415, '#skF_3') | ~m1_subset_1(D_415, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v5_pre_topc('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_173, c_2880])).
% 5.61/2.04  tff(c_2890, plain, (![D_416]: (v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4'), '#skF_5', D_416), '#skF_2') | ~v3_pre_topc(D_416, '#skF_3') | ~m1_subset_1(D_416, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_117, c_40, c_2882])).
% 5.61/2.04  tff(c_1195, plain, (![B_189, A_190, C_191]: (k2_struct_0(B_189)=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_190), u1_struct_0(B_189), C_191, '#skF_1'(A_190, B_189, C_191)), A_190) | v5_pre_topc(C_191, A_190, B_189) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190), u1_struct_0(B_189)))) | ~v1_funct_2(C_191, u1_struct_0(A_190), u1_struct_0(B_189)) | ~v1_funct_1(C_191) | ~l1_pre_topc(B_189) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.61/2.04  tff(c_1207, plain, (![A_190, C_191]: (k2_struct_0('#skF_4')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_190), k2_struct_0('#skF_4'), C_191, '#skF_1'(A_190, '#skF_4', C_191)), A_190) | v5_pre_topc(C_191, A_190, '#skF_4') | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_191, u1_struct_0(A_190), u1_struct_0('#skF_4')) | ~v1_funct_1(C_191) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_190))), inference(superposition, [status(thm), theory('equality')], [c_93, c_1195])).
% 5.61/2.04  tff(c_1222, plain, (![A_190, C_191]: (k2_struct_0('#skF_4')=k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_190), k2_struct_0('#skF_4'), C_191, '#skF_1'(A_190, '#skF_4', C_191)), A_190) | v5_pre_topc(C_191, A_190, '#skF_4') | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_191, u1_struct_0(A_190), k2_struct_0('#skF_4')) | ~v1_funct_1(C_191) | ~l1_pre_topc(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_93, c_93, c_1207])).
% 5.61/2.04  tff(c_2560, plain, (![A_358, C_359]: (~v3_pre_topc(k8_relset_1(u1_struct_0(A_358), k2_struct_0('#skF_4'), C_359, '#skF_1'(A_358, '#skF_4', C_359)), A_358) | v5_pre_topc(C_359, A_358, '#skF_4') | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_358), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_359, u1_struct_0(A_358), k2_struct_0('#skF_4')) | ~v1_funct_1(C_359) | ~l1_pre_topc(A_358))), inference(negUnitSimplification, [status(thm)], [c_381, c_1222])).
% 5.61/2.04  tff(c_2569, plain, (![C_359]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4'), C_359, '#skF_1'('#skF_2', '#skF_4', C_359)), '#skF_2') | v5_pre_topc(C_359, '#skF_2', '#skF_4') | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_359, u1_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_359) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_2560])).
% 5.61/2.04  tff(c_2575, plain, (![C_359]: (~v3_pre_topc(k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4'), C_359, '#skF_1'('#skF_2', '#skF_4', C_359)), '#skF_2') | v5_pre_topc(C_359, '#skF_2', '#skF_4') | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4')))) | ~v1_funct_2(C_359, k2_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1(C_359))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91, c_91, c_2569])).
% 5.61/2.04  tff(c_2894, plain, (v5_pre_topc('#skF_5', '#skF_2', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', k2_struct_0('#skF_2'), k2_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_4', '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2890, c_2575])).
% 5.61/2.04  tff(c_2901, plain, (v5_pre_topc('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_625, c_1194, c_44, c_117, c_173, c_2894])).
% 5.61/2.04  tff(c_2903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_2901])).
% 5.61/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.61/2.04  
% 5.61/2.04  Inference rules
% 5.61/2.04  ----------------------
% 5.61/2.04  #Ref     : 0
% 5.61/2.04  #Sup     : 532
% 5.61/2.04  #Fact    : 0
% 5.61/2.04  #Define  : 0
% 5.61/2.04  #Split   : 17
% 5.61/2.04  #Chain   : 0
% 5.61/2.04  #Close   : 0
% 5.61/2.04  
% 5.61/2.04  Ordering : KBO
% 5.61/2.04  
% 5.61/2.04  Simplification rules
% 5.61/2.04  ----------------------
% 5.61/2.04  #Subsume      : 196
% 5.61/2.04  #Demod        : 993
% 5.61/2.04  #Tautology    : 70
% 5.61/2.04  #SimpNegUnit  : 110
% 5.61/2.04  #BackRed      : 18
% 5.61/2.04  
% 5.61/2.04  #Partial instantiations: 0
% 5.61/2.04  #Strategies tried      : 1
% 5.61/2.04  
% 5.61/2.04  Timing (in seconds)
% 5.61/2.04  ----------------------
% 5.61/2.04  Preprocessing        : 0.32
% 5.61/2.04  Parsing              : 0.17
% 5.61/2.04  CNF conversion       : 0.02
% 5.61/2.04  Main loop            : 0.95
% 5.61/2.04  Inferencing          : 0.33
% 5.61/2.04  Reduction            : 0.35
% 5.61/2.04  Demodulation         : 0.25
% 5.61/2.04  BG Simplification    : 0.03
% 5.61/2.04  Subsumption          : 0.17
% 5.61/2.04  Abstraction          : 0.03
% 5.61/2.04  MUC search           : 0.00
% 5.61/2.04  Cooper               : 0.00
% 5.61/2.04  Total                : 1.32
% 5.61/2.04  Index Insertion      : 0.00
% 5.61/2.04  Index Deletion       : 0.00
% 5.61/2.04  Index Matching       : 0.00
% 5.61/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
