%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:30 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 145 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 ( 321 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(resolution,[status(thm)],[c_16,c_54])).

tff(c_184,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_196,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k5_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_184])).

tff(c_200,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_196])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_201,plain,(
    ! [B_61,A_62] :
      ( v1_subset_1(B_61,A_62)
      | B_61 = A_62
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_205,plain,(
    ! [A_16,B_17] :
      ( v1_subset_1(A_16,B_17)
      | B_17 = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_201])).

tff(c_287,plain,(
    ! [B_71,A_72] :
      ( ~ v1_subset_1(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_292,plain,(
    ! [A_73,B_74] :
      ( ~ v1_subset_1(A_73,B_74)
      | ~ v1_xboole_0(B_74)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_22,c_287])).

tff(c_297,plain,(
    ! [B_75,A_76] :
      ( ~ v1_xboole_0(B_75)
      | B_75 = A_76
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(resolution,[status(thm)],[c_205,c_292])).

tff(c_321,plain,(
    ! [A_79,B_80] :
      ( ~ v1_xboole_0(A_79)
      | k3_xboole_0(A_79,B_80) = A_79 ) ),
    inference(resolution,[status(thm)],[c_10,c_297])).

tff(c_325,plain,(
    ! [B_81] : k3_xboole_0(k1_xboole_0,B_81) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_321])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_333,plain,(
    ! [B_81] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_8])).

tff(c_360,plain,(
    ! [B_81] : k4_xboole_0(k1_xboole_0,B_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_333])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_315,plain,(
    ! [B_77,A_78] :
      ( v2_tex_2(B_77,A_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v1_xboole_0(B_77)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_425,plain,(
    ! [A_88,A_89] :
      ( v2_tex_2(A_88,A_89)
      | ~ v1_xboole_0(A_88)
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89)
      | ~ r1_tarski(A_88,u1_struct_0(A_89)) ) ),
    inference(resolution,[status(thm)],[c_22,c_315])).

tff(c_447,plain,(
    ! [A_93,A_94] :
      ( v2_tex_2(A_93,A_94)
      | ~ v1_xboole_0(A_93)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94)
      | k4_xboole_0(A_93,u1_struct_0(A_94)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_425])).

tff(c_451,plain,(
    ! [A_94] :
      ( v2_tex_2(k1_xboole_0,A_94)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_447])).

tff(c_462,plain,(
    ! [A_94] :
      ( v2_tex_2(k1_xboole_0,A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_451])).

tff(c_40,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_477,plain,(
    ! [A_98,B_99] :
      ( v3_tex_2('#skF_1'(A_98,B_99),A_98)
      | ~ v2_tex_2(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98)
      | ~ v3_tdlat_3(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_481,plain,(
    ! [A_98,A_16] :
      ( v3_tex_2('#skF_1'(A_98,A_16),A_98)
      | ~ v2_tex_2(A_16,A_98)
      | ~ l1_pre_topc(A_98)
      | ~ v3_tdlat_3(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98)
      | ~ r1_tarski(A_16,u1_struct_0(A_98)) ) ),
    inference(resolution,[status(thm)],[c_22,c_477])).

tff(c_522,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1('#skF_1'(A_106,B_107),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v3_tdlat_3(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    ! [B_30] :
      ( ~ v3_tex_2(B_30,'#skF_2')
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_542,plain,(
    ! [B_107] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_107),'#skF_2')
      | ~ v2_tex_2(B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_522,c_36])).

tff(c_551,plain,(
    ! [B_107] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_107),'#skF_2')
      | ~ v2_tex_2(B_107,'#skF_2')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_542])).

tff(c_553,plain,(
    ! [B_108] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_108),'#skF_2')
      | ~ v2_tex_2(B_108,'#skF_2')
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_551])).

tff(c_567,plain,(
    ! [A_109] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',A_109),'#skF_2')
      | ~ v2_tex_2(A_109,'#skF_2')
      | ~ r1_tarski(A_109,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22,c_553])).

tff(c_571,plain,(
    ! [A_16] :
      ( ~ v2_tex_2(A_16,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_16,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_481,c_567])).

tff(c_574,plain,(
    ! [A_16] :
      ( ~ v2_tex_2(A_16,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_16,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_571])).

tff(c_576,plain,(
    ! [A_110] :
      ( ~ v2_tex_2(A_110,'#skF_2')
      | ~ r1_tarski(A_110,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_574])).

tff(c_633,plain,(
    ! [A_114] :
      ( ~ v2_tex_2(A_114,'#skF_2')
      | k4_xboole_0(A_114,u1_struct_0('#skF_2')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_576])).

tff(c_646,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_633])).

tff(c_687,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_462,c_646])).

tff(c_690,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_687])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.37  
% 2.78/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.37  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.78/1.37  
% 2.78/1.37  %Foreground sorts:
% 2.78/1.37  
% 2.78/1.37  
% 2.78/1.37  %Background operators:
% 2.78/1.37  
% 2.78/1.37  
% 2.78/1.37  %Foreground operators:
% 2.78/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.78/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.37  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.78/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.78/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.37  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.78/1.37  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.78/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.37  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.78/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.78/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.37  
% 2.78/1.39  tff(f_113, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.78/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.78/1.39  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.78/1.39  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.78/1.39  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.78/1.39  tff(f_32, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.78/1.39  tff(f_34, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.78/1.39  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.78/1.39  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.78/1.39  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 2.78/1.39  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.78/1.39  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.78/1.39  tff(f_98, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.78/1.39  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.39  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.39  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.78/1.39  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.78/1.39  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.78/1.39  tff(c_54, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.78/1.39  tff(c_61, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(resolution, [status(thm)], [c_16, c_54])).
% 2.78/1.39  tff(c_184, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.39  tff(c_196, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k5_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_61, c_184])).
% 2.78/1.39  tff(c_200, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_196])).
% 2.78/1.39  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.78/1.39  tff(c_22, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.78/1.39  tff(c_201, plain, (![B_61, A_62]: (v1_subset_1(B_61, A_62) | B_61=A_62 | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.78/1.39  tff(c_205, plain, (![A_16, B_17]: (v1_subset_1(A_16, B_17) | B_17=A_16 | ~r1_tarski(A_16, B_17))), inference(resolution, [status(thm)], [c_22, c_201])).
% 2.78/1.39  tff(c_287, plain, (![B_71, A_72]: (~v1_subset_1(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.78/1.39  tff(c_292, plain, (![A_73, B_74]: (~v1_subset_1(A_73, B_74) | ~v1_xboole_0(B_74) | ~r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_22, c_287])).
% 2.78/1.39  tff(c_297, plain, (![B_75, A_76]: (~v1_xboole_0(B_75) | B_75=A_76 | ~r1_tarski(A_76, B_75))), inference(resolution, [status(thm)], [c_205, c_292])).
% 2.78/1.39  tff(c_321, plain, (![A_79, B_80]: (~v1_xboole_0(A_79) | k3_xboole_0(A_79, B_80)=A_79)), inference(resolution, [status(thm)], [c_10, c_297])).
% 2.78/1.39  tff(c_325, plain, (![B_81]: (k3_xboole_0(k1_xboole_0, B_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_321])).
% 2.78/1.39  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.39  tff(c_333, plain, (![B_81]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_81))), inference(superposition, [status(thm), theory('equality')], [c_325, c_8])).
% 2.78/1.39  tff(c_360, plain, (![B_81]: (k4_xboole_0(k1_xboole_0, B_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_333])).
% 2.78/1.39  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.78/1.39  tff(c_315, plain, (![B_77, A_78]: (v2_tex_2(B_77, A_78) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~v1_xboole_0(B_77) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.39  tff(c_425, plain, (![A_88, A_89]: (v2_tex_2(A_88, A_89) | ~v1_xboole_0(A_88) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89) | ~r1_tarski(A_88, u1_struct_0(A_89)))), inference(resolution, [status(thm)], [c_22, c_315])).
% 2.78/1.39  tff(c_447, plain, (![A_93, A_94]: (v2_tex_2(A_93, A_94) | ~v1_xboole_0(A_93) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94) | k4_xboole_0(A_93, u1_struct_0(A_94))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_425])).
% 2.78/1.39  tff(c_451, plain, (![A_94]: (v2_tex_2(k1_xboole_0, A_94) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(superposition, [status(thm), theory('equality')], [c_360, c_447])).
% 2.78/1.39  tff(c_462, plain, (![A_94]: (v2_tex_2(k1_xboole_0, A_94) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_451])).
% 2.78/1.39  tff(c_40, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.39  tff(c_477, plain, (![A_98, B_99]: (v3_tex_2('#skF_1'(A_98, B_99), A_98) | ~v2_tex_2(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98) | ~v3_tdlat_3(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.78/1.39  tff(c_481, plain, (![A_98, A_16]: (v3_tex_2('#skF_1'(A_98, A_16), A_98) | ~v2_tex_2(A_16, A_98) | ~l1_pre_topc(A_98) | ~v3_tdlat_3(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98) | ~r1_tarski(A_16, u1_struct_0(A_98)))), inference(resolution, [status(thm)], [c_22, c_477])).
% 2.78/1.39  tff(c_522, plain, (![A_106, B_107]: (m1_subset_1('#skF_1'(A_106, B_107), k1_zfmisc_1(u1_struct_0(A_106))) | ~v2_tex_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v3_tdlat_3(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.78/1.39  tff(c_36, plain, (![B_30]: (~v3_tex_2(B_30, '#skF_2') | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.39  tff(c_542, plain, (![B_107]: (~v3_tex_2('#skF_1'('#skF_2', B_107), '#skF_2') | ~v2_tex_2(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_522, c_36])).
% 2.78/1.39  tff(c_551, plain, (![B_107]: (~v3_tex_2('#skF_1'('#skF_2', B_107), '#skF_2') | ~v2_tex_2(B_107, '#skF_2') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_542])).
% 2.78/1.39  tff(c_553, plain, (![B_108]: (~v3_tex_2('#skF_1'('#skF_2', B_108), '#skF_2') | ~v2_tex_2(B_108, '#skF_2') | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_551])).
% 2.78/1.39  tff(c_567, plain, (![A_109]: (~v3_tex_2('#skF_1'('#skF_2', A_109), '#skF_2') | ~v2_tex_2(A_109, '#skF_2') | ~r1_tarski(A_109, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_553])).
% 2.78/1.39  tff(c_571, plain, (![A_16]: (~v2_tex_2(A_16, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_16, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_481, c_567])).
% 2.78/1.39  tff(c_574, plain, (![A_16]: (~v2_tex_2(A_16, '#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_16, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_571])).
% 2.78/1.39  tff(c_576, plain, (![A_110]: (~v2_tex_2(A_110, '#skF_2') | ~r1_tarski(A_110, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_574])).
% 2.78/1.39  tff(c_633, plain, (![A_114]: (~v2_tex_2(A_114, '#skF_2') | k4_xboole_0(A_114, u1_struct_0('#skF_2'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_576])).
% 2.78/1.39  tff(c_646, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_360, c_633])).
% 2.78/1.39  tff(c_687, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_462, c_646])).
% 2.78/1.39  tff(c_690, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_687])).
% 2.78/1.39  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_690])).
% 2.78/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.39  
% 2.78/1.39  Inference rules
% 2.78/1.39  ----------------------
% 2.78/1.39  #Ref     : 0
% 2.78/1.39  #Sup     : 132
% 2.78/1.39  #Fact    : 0
% 2.78/1.39  #Define  : 0
% 2.78/1.39  #Split   : 0
% 2.78/1.39  #Chain   : 0
% 2.78/1.39  #Close   : 0
% 2.78/1.39  
% 2.78/1.39  Ordering : KBO
% 2.78/1.39  
% 2.78/1.39  Simplification rules
% 2.78/1.39  ----------------------
% 2.78/1.39  #Subsume      : 18
% 2.78/1.39  #Demod        : 58
% 2.78/1.39  #Tautology    : 56
% 2.78/1.39  #SimpNegUnit  : 9
% 2.78/1.39  #BackRed      : 0
% 2.78/1.39  
% 2.78/1.39  #Partial instantiations: 0
% 2.78/1.39  #Strategies tried      : 1
% 2.78/1.39  
% 2.78/1.39  Timing (in seconds)
% 2.78/1.39  ----------------------
% 2.78/1.39  Preprocessing        : 0.31
% 2.78/1.39  Parsing              : 0.18
% 2.78/1.39  CNF conversion       : 0.02
% 2.78/1.39  Main loop            : 0.31
% 2.78/1.39  Inferencing          : 0.13
% 2.78/1.39  Reduction            : 0.09
% 2.78/1.39  Demodulation         : 0.06
% 2.78/1.39  BG Simplification    : 0.02
% 2.78/1.39  Subsumption          : 0.06
% 2.78/1.39  Abstraction          : 0.01
% 2.78/1.39  MUC search           : 0.00
% 2.78/1.39  Cooper               : 0.00
% 2.78/1.39  Total                : 0.66
% 2.78/1.39  Index Insertion      : 0.00
% 2.78/1.39  Index Deletion       : 0.00
% 2.78/1.39  Index Matching       : 0.00
% 2.78/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
