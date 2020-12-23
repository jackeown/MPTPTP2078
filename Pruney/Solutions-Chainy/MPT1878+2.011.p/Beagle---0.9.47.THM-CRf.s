%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:59 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 133 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :   19
%              Number of atoms          :  173 ( 318 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_40,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_155,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(A_56,B_57) = k1_tarski(B_57)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_163,plain,(
    ! [A_6] :
      ( k6_domain_1(A_6,'#skF_1'(A_6)) = k1_tarski('#skF_1'(A_6))
      | v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_155])).

tff(c_270,plain,(
    ! [A_76,B_77] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_76),B_77),A_76)
      | ~ m1_subset_1(B_77,u1_struct_0(A_76))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_274,plain,(
    ! [A_76] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_76))),A_76)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_76)),u1_struct_0(A_76))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76)
      | v1_xboole_0(u1_struct_0(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_270])).

tff(c_276,plain,(
    ! [A_76] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_76))),A_76)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76)
      | v1_xboole_0(u1_struct_0(A_76)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_274])).

tff(c_67,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_76,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_67])).

tff(c_6,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_45] : k2_xboole_0(A_45,'#skF_5') = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6])).

tff(c_10,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),B_5) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),B_5) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10])).

tff(c_105,plain,(
    ! [A_4] : k1_tarski(A_4) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_94])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(k1_tarski(B_10),k1_zfmisc_1(A_9))
      | k1_xboole_0 = A_9
      | ~ m1_subset_1(B_10,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_181,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(k1_tarski(B_10),k1_zfmisc_1(A_9))
      | A_9 = '#skF_5'
      | ~ m1_subset_1(B_10,A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_16])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8])).

tff(c_478,plain,(
    ! [C_107,B_108,A_109] :
      ( C_107 = B_108
      | ~ r1_tarski(B_108,C_107)
      | ~ v2_tex_2(C_107,A_109)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ v3_tex_2(B_108,A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_480,plain,(
    ! [A_3,A_109] :
      ( A_3 = '#skF_5'
      | ~ v2_tex_2(A_3,A_109)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ v3_tex_2('#skF_5',A_109)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_80,c_478])).

tff(c_485,plain,(
    ! [A_111,A_112] :
      ( A_111 = '#skF_5'
      | ~ v2_tex_2(A_111,A_112)
      | ~ m1_subset_1(A_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v3_tex_2('#skF_5',A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_480])).

tff(c_499,plain,(
    ! [B_10,A_112] :
      ( k1_tarski(B_10) = '#skF_5'
      | ~ v2_tex_2(k1_tarski(B_10),A_112)
      | ~ v3_tex_2('#skF_5',A_112)
      | ~ l1_pre_topc(A_112)
      | u1_struct_0(A_112) = '#skF_5'
      | ~ m1_subset_1(B_10,u1_struct_0(A_112)) ) ),
    inference(resolution,[status(thm)],[c_181,c_485])).

tff(c_526,plain,(
    ! [B_115,A_116] :
      ( ~ v2_tex_2(k1_tarski(B_115),A_116)
      | ~ v3_tex_2('#skF_5',A_116)
      | ~ l1_pre_topc(A_116)
      | u1_struct_0(A_116) = '#skF_5'
      | ~ m1_subset_1(B_115,u1_struct_0(A_116)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_499])).

tff(c_529,plain,(
    ! [A_76] :
      ( ~ v3_tex_2('#skF_5',A_76)
      | u1_struct_0(A_76) = '#skF_5'
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_76)),u1_struct_0(A_76))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76)
      | v1_xboole_0(u1_struct_0(A_76)) ) ),
    inference(resolution,[status(thm)],[c_276,c_526])).

tff(c_537,plain,(
    ! [A_118] :
      ( ~ v3_tex_2('#skF_5',A_118)
      | u1_struct_0(A_118) = '#skF_5'
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118)
      | v1_xboole_0(u1_struct_0(A_118)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_529])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_77,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4])).

tff(c_550,plain,(
    ! [A_119] :
      ( ~ v3_tex_2('#skF_5',A_119)
      | u1_struct_0(A_119) = '#skF_5'
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_537,c_77])).

tff(c_556,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_550])).

tff(c_560,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_556])).

tff(c_561,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_560])).

tff(c_208,plain,(
    ! [A_67] :
      ( m1_subset_1('#skF_2'(A_67),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    ! [B_13,A_11] :
      ( v1_xboole_0(B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_11))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_219,plain,(
    ! [A_67] :
      ( v1_xboole_0('#skF_2'(A_67))
      | ~ v1_xboole_0(u1_struct_0(A_67))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_208,c_18])).

tff(c_605,plain,
    ( v1_xboole_0('#skF_2'('#skF_4'))
    | ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_219])).

tff(c_643,plain,
    ( v1_xboole_0('#skF_2'('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_605])).

tff(c_644,plain,(
    v1_xboole_0('#skF_2'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_643])).

tff(c_24,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_2'(A_17))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_651,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_644,c_24])).

tff(c_657,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_651])).

tff(c_659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:18:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.45  
% 2.83/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.45  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 2.83/1.45  
% 2.83/1.45  %Foreground sorts:
% 2.83/1.45  
% 2.83/1.45  
% 2.83/1.45  %Background operators:
% 2.83/1.45  
% 2.83/1.45  
% 2.83/1.45  %Foreground operators:
% 2.83/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.83/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.83/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.83/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.83/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.45  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.83/1.45  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.83/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.83/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.83/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.45  
% 2.98/1.47  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 2.98/1.47  tff(f_40, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.98/1.47  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.98/1.47  tff(f_114, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.98/1.47  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.98/1.47  tff(f_32, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.98/1.47  tff(f_37, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.98/1.47  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.98/1.47  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.98/1.47  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.98/1.47  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.98/1.47  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 2.98/1.47  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.98/1.47  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.98/1.47  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.98/1.47  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.98/1.47  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.98/1.47  tff(c_44, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.98/1.47  tff(c_12, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.98/1.47  tff(c_155, plain, (![A_56, B_57]: (k6_domain_1(A_56, B_57)=k1_tarski(B_57) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.98/1.47  tff(c_163, plain, (![A_6]: (k6_domain_1(A_6, '#skF_1'(A_6))=k1_tarski('#skF_1'(A_6)) | v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_12, c_155])).
% 2.98/1.47  tff(c_270, plain, (![A_76, B_77]: (v2_tex_2(k6_domain_1(u1_struct_0(A_76), B_77), A_76) | ~m1_subset_1(B_77, u1_struct_0(A_76)) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.98/1.47  tff(c_274, plain, (![A_76]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_76))), A_76) | ~m1_subset_1('#skF_1'(u1_struct_0(A_76)), u1_struct_0(A_76)) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76) | v1_xboole_0(u1_struct_0(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_270])).
% 2.98/1.47  tff(c_276, plain, (![A_76]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_76))), A_76) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76) | v1_xboole_0(u1_struct_0(A_76)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_274])).
% 2.98/1.47  tff(c_67, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.98/1.47  tff(c_76, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_67])).
% 2.98/1.47  tff(c_6, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.47  tff(c_98, plain, (![A_45]: (k2_xboole_0(A_45, '#skF_5')=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6])).
% 2.98/1.47  tff(c_10, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.47  tff(c_94, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10])).
% 2.98/1.47  tff(c_105, plain, (![A_4]: (k1_tarski(A_4)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_98, c_94])).
% 2.98/1.47  tff(c_16, plain, (![B_10, A_9]: (m1_subset_1(k1_tarski(B_10), k1_zfmisc_1(A_9)) | k1_xboole_0=A_9 | ~m1_subset_1(B_10, A_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.98/1.47  tff(c_181, plain, (![B_10, A_9]: (m1_subset_1(k1_tarski(B_10), k1_zfmisc_1(A_9)) | A_9='#skF_5' | ~m1_subset_1(B_10, A_9))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_16])).
% 2.98/1.47  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.98/1.47  tff(c_78, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_14])).
% 2.98/1.47  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.98/1.47  tff(c_80, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8])).
% 2.98/1.47  tff(c_478, plain, (![C_107, B_108, A_109]: (C_107=B_108 | ~r1_tarski(B_108, C_107) | ~v2_tex_2(C_107, A_109) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_109))) | ~v3_tex_2(B_108, A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.98/1.47  tff(c_480, plain, (![A_3, A_109]: (A_3='#skF_5' | ~v2_tex_2(A_3, A_109) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_109))) | ~v3_tex_2('#skF_5', A_109) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_80, c_478])).
% 2.98/1.47  tff(c_485, plain, (![A_111, A_112]: (A_111='#skF_5' | ~v2_tex_2(A_111, A_112) | ~m1_subset_1(A_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~v3_tex_2('#skF_5', A_112) | ~l1_pre_topc(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_480])).
% 2.98/1.47  tff(c_499, plain, (![B_10, A_112]: (k1_tarski(B_10)='#skF_5' | ~v2_tex_2(k1_tarski(B_10), A_112) | ~v3_tex_2('#skF_5', A_112) | ~l1_pre_topc(A_112) | u1_struct_0(A_112)='#skF_5' | ~m1_subset_1(B_10, u1_struct_0(A_112)))), inference(resolution, [status(thm)], [c_181, c_485])).
% 2.98/1.47  tff(c_526, plain, (![B_115, A_116]: (~v2_tex_2(k1_tarski(B_115), A_116) | ~v3_tex_2('#skF_5', A_116) | ~l1_pre_topc(A_116) | u1_struct_0(A_116)='#skF_5' | ~m1_subset_1(B_115, u1_struct_0(A_116)))), inference(negUnitSimplification, [status(thm)], [c_105, c_499])).
% 2.98/1.47  tff(c_529, plain, (![A_76]: (~v3_tex_2('#skF_5', A_76) | u1_struct_0(A_76)='#skF_5' | ~m1_subset_1('#skF_1'(u1_struct_0(A_76)), u1_struct_0(A_76)) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76) | v1_xboole_0(u1_struct_0(A_76)))), inference(resolution, [status(thm)], [c_276, c_526])).
% 2.98/1.47  tff(c_537, plain, (![A_118]: (~v3_tex_2('#skF_5', A_118) | u1_struct_0(A_118)='#skF_5' | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118) | v1_xboole_0(u1_struct_0(A_118)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_529])).
% 2.98/1.47  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.98/1.47  tff(c_77, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4])).
% 2.98/1.47  tff(c_550, plain, (![A_119]: (~v3_tex_2('#skF_5', A_119) | u1_struct_0(A_119)='#skF_5' | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(resolution, [status(thm)], [c_537, c_77])).
% 2.98/1.47  tff(c_556, plain, (u1_struct_0('#skF_4')='#skF_5' | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_550])).
% 2.98/1.47  tff(c_560, plain, (u1_struct_0('#skF_4')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_556])).
% 2.98/1.47  tff(c_561, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_560])).
% 2.98/1.47  tff(c_208, plain, (![A_67]: (m1_subset_1('#skF_2'(A_67), k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.98/1.47  tff(c_18, plain, (![B_13, A_11]: (v1_xboole_0(B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_11)) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.98/1.47  tff(c_219, plain, (![A_67]: (v1_xboole_0('#skF_2'(A_67)) | ~v1_xboole_0(u1_struct_0(A_67)) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_208, c_18])).
% 2.98/1.47  tff(c_605, plain, (v1_xboole_0('#skF_2'('#skF_4')) | ~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_561, c_219])).
% 2.98/1.47  tff(c_643, plain, (v1_xboole_0('#skF_2'('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_605])).
% 2.98/1.47  tff(c_644, plain, (v1_xboole_0('#skF_2'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_643])).
% 2.98/1.47  tff(c_24, plain, (![A_17]: (~v1_xboole_0('#skF_2'(A_17)) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.98/1.47  tff(c_651, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_644, c_24])).
% 2.98/1.47  tff(c_657, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_651])).
% 2.98/1.47  tff(c_659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_657])).
% 2.98/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.47  
% 2.98/1.47  Inference rules
% 2.98/1.47  ----------------------
% 2.98/1.47  #Ref     : 0
% 2.98/1.47  #Sup     : 129
% 2.98/1.47  #Fact    : 0
% 2.98/1.47  #Define  : 0
% 2.98/1.47  #Split   : 0
% 2.98/1.47  #Chain   : 0
% 2.98/1.47  #Close   : 0
% 2.98/1.47  
% 2.98/1.47  Ordering : KBO
% 2.98/1.47  
% 2.98/1.47  Simplification rules
% 2.98/1.47  ----------------------
% 2.98/1.47  #Subsume      : 14
% 2.98/1.47  #Demod        : 60
% 2.98/1.47  #Tautology    : 33
% 2.98/1.47  #SimpNegUnit  : 8
% 2.98/1.47  #BackRed      : 5
% 2.98/1.47  
% 2.98/1.47  #Partial instantiations: 0
% 2.98/1.47  #Strategies tried      : 1
% 2.98/1.47  
% 2.98/1.47  Timing (in seconds)
% 2.98/1.47  ----------------------
% 2.98/1.47  Preprocessing        : 0.33
% 2.98/1.47  Parsing              : 0.18
% 2.98/1.47  CNF conversion       : 0.02
% 2.98/1.47  Main loop            : 0.33
% 2.98/1.47  Inferencing          : 0.13
% 2.98/1.47  Reduction            : 0.10
% 2.98/1.47  Demodulation         : 0.06
% 2.98/1.47  BG Simplification    : 0.02
% 2.98/1.47  Subsumption          : 0.07
% 2.98/1.47  Abstraction          : 0.02
% 2.98/1.47  MUC search           : 0.00
% 2.98/1.47  Cooper               : 0.00
% 2.98/1.47  Total                : 0.69
% 2.98/1.47  Index Insertion      : 0.00
% 2.98/1.47  Index Deletion       : 0.00
% 2.98/1.47  Index Matching       : 0.00
% 2.98/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
