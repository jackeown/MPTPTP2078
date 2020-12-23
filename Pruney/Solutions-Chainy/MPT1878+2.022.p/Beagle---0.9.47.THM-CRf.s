%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:00 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 113 expanded)
%              Number of leaves         :   39 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  178 ( 266 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_103,axiom,(
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

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_65,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_5') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_8])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),B_9) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    ! [A_46,B_47] : k2_xboole_0(k1_tarski(A_46),B_47) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_103,plain,(
    ! [A_46] : k1_tarski(A_46) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_10] :
      ( m1_subset_1('#skF_2'(A_10),k1_zfmisc_1(A_10))
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [A_53,C_54,B_55] :
      ( m1_subset_1(A_53,C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_126,plain,(
    ! [A_58,A_59] :
      ( m1_subset_1(A_58,A_59)
      | ~ r2_hidden(A_58,'#skF_2'(A_59))
      | v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_16,c_113])).

tff(c_131,plain,(
    ! [A_59] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_59)),A_59)
      | v1_xboole_0(A_59)
      | v1_xboole_0('#skF_2'(A_59)) ) ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_42,plain,(
    ! [A_32,B_34] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_32),B_34),A_32)
      | ~ m1_subset_1(B_34,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k6_domain_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [A_12] : m1_subset_1('#skF_5',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_18])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_7] : r1_tarski('#skF_5',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_610,plain,(
    ! [C_106,B_107,A_108] :
      ( C_106 = B_107
      | ~ r1_tarski(B_107,C_106)
      | ~ v2_tex_2(C_106,A_108)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ v3_tex_2(B_107,A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_612,plain,(
    ! [A_7,A_108] :
      ( A_7 = '#skF_5'
      | ~ v2_tex_2(A_7,A_108)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ v3_tex_2('#skF_5',A_108)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_72,c_610])).

tff(c_616,plain,(
    ! [A_109,A_110] :
      ( A_109 = '#skF_5'
      | ~ v2_tex_2(A_109,A_110)
      | ~ m1_subset_1(A_109,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ v3_tex_2('#skF_5',A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_612])).

tff(c_912,plain,(
    ! [A_138,B_139] :
      ( k6_domain_1(u1_struct_0(A_138),B_139) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_138),B_139),A_138)
      | ~ v3_tex_2('#skF_5',A_138)
      | ~ l1_pre_topc(A_138)
      | ~ m1_subset_1(B_139,u1_struct_0(A_138))
      | v1_xboole_0(u1_struct_0(A_138)) ) ),
    inference(resolution,[status(thm)],[c_26,c_616])).

tff(c_925,plain,(
    ! [A_140,B_141] :
      ( k6_domain_1(u1_struct_0(A_140),B_141) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_140)
      | v1_xboole_0(u1_struct_0(A_140))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_42,c_912])).

tff(c_966,plain,(
    ! [A_147] :
      ( k6_domain_1(u1_struct_0(A_147),'#skF_1'('#skF_2'(u1_struct_0(A_147)))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_147)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | v1_xboole_0(u1_struct_0(A_147))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_147))) ) ),
    inference(resolution,[status(thm)],[c_131,c_925])).

tff(c_155,plain,(
    ! [A_64] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_64)),A_64)
      | v1_xboole_0(A_64)
      | v1_xboole_0('#skF_2'(A_64)) ) ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( k6_domain_1(A_20,B_21) = k1_tarski(B_21)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_162,plain,(
    ! [A_64] :
      ( k6_domain_1(A_64,'#skF_1'('#skF_2'(A_64))) = k1_tarski('#skF_1'('#skF_2'(A_64)))
      | v1_xboole_0(A_64)
      | v1_xboole_0('#skF_2'(A_64)) ) ),
    inference(resolution,[status(thm)],[c_155,c_28])).

tff(c_987,plain,(
    ! [A_147] :
      ( k1_tarski('#skF_1'('#skF_2'(u1_struct_0(A_147)))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_147))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_147)))
      | ~ v3_tex_2('#skF_5',A_147)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | v1_xboole_0(u1_struct_0(A_147))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_147))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_162])).

tff(c_1004,plain,(
    ! [A_147] :
      ( v1_xboole_0(u1_struct_0(A_147))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_147)))
      | ~ v3_tex_2('#skF_5',A_147)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | v1_xboole_0(u1_struct_0(A_147))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_147))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_987])).

tff(c_1050,plain,(
    ! [A_151] :
      ( ~ v3_tex_2('#skF_5',A_151)
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151)
      | v1_xboole_0(u1_struct_0(A_151))
      | v1_xboole_0('#skF_2'(u1_struct_0(A_151))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1004])).

tff(c_14,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0('#skF_2'(A_10))
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1059,plain,(
    ! [A_152] :
      ( ~ v3_tex_2('#skF_5',A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152)
      | v1_xboole_0(u1_struct_0(A_152)) ) ),
    inference(resolution,[status(thm)],[c_1050,c_14])).

tff(c_24,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1068,plain,(
    ! [A_153] :
      ( ~ l1_struct_0(A_153)
      | ~ v3_tex_2('#skF_5',A_153)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_1059,c_24])).

tff(c_1074,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1068])).

tff(c_1078,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1074])).

tff(c_1079,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1078])).

tff(c_1082,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1079])).

tff(c_1086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/2.24  
% 4.85/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/2.24  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 4.85/2.24  
% 4.85/2.24  %Foreground sorts:
% 4.85/2.24  
% 4.85/2.24  
% 4.85/2.24  %Background operators:
% 4.85/2.24  
% 4.85/2.24  
% 4.85/2.24  %Foreground operators:
% 4.85/2.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.85/2.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.85/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.85/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.85/2.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.85/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.85/2.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.85/2.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.85/2.24  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.85/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.85/2.24  tff('#skF_5', type, '#skF_5': $i).
% 4.85/2.24  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.85/2.24  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.85/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.85/2.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.85/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/2.24  tff('#skF_4', type, '#skF_4': $i).
% 4.85/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/2.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.85/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.85/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.85/2.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.85/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.85/2.24  
% 4.85/2.27  tff(f_131, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 4.85/2.27  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.85/2.27  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.85/2.27  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.85/2.27  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.85/2.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.85/2.27  tff(f_51, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_subset_1)).
% 4.85/2.27  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.85/2.27  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 4.85/2.27  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.85/2.27  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.85/2.27  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.85/2.27  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.85/2.27  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.85/2.27  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.85/2.27  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.85/2.27  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.85/2.27  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.85/2.27  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.85/2.27  tff(c_44, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.85/2.27  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.85/2.27  tff(c_65, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.85/2.27  tff(c_69, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_65])).
% 4.85/2.27  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.85/2.27  tff(c_71, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_5')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_69, c_8])).
% 4.85/2.27  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.85/2.27  tff(c_99, plain, (![A_46, B_47]: (k2_xboole_0(k1_tarski(A_46), B_47)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_12])).
% 4.85/2.27  tff(c_103, plain, (![A_46]: (k1_tarski(A_46)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_71, c_99])).
% 4.85/2.27  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.85/2.27  tff(c_16, plain, (![A_10]: (m1_subset_1('#skF_2'(A_10), k1_zfmisc_1(A_10)) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.85/2.27  tff(c_113, plain, (![A_53, C_54, B_55]: (m1_subset_1(A_53, C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.85/2.27  tff(c_126, plain, (![A_58, A_59]: (m1_subset_1(A_58, A_59) | ~r2_hidden(A_58, '#skF_2'(A_59)) | v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_16, c_113])).
% 4.85/2.27  tff(c_131, plain, (![A_59]: (m1_subset_1('#skF_1'('#skF_2'(A_59)), A_59) | v1_xboole_0(A_59) | v1_xboole_0('#skF_2'(A_59)))), inference(resolution, [status(thm)], [c_4, c_126])).
% 4.85/2.27  tff(c_42, plain, (![A_32, B_34]: (v2_tex_2(k6_domain_1(u1_struct_0(A_32), B_34), A_32) | ~m1_subset_1(B_34, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.85/2.27  tff(c_26, plain, (![A_18, B_19]: (m1_subset_1(k6_domain_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.85/2.27  tff(c_18, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.85/2.27  tff(c_78, plain, (![A_12]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_18])).
% 4.85/2.27  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.85/2.27  tff(c_72, plain, (![A_7]: (r1_tarski('#skF_5', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_10])).
% 4.85/2.27  tff(c_610, plain, (![C_106, B_107, A_108]: (C_106=B_107 | ~r1_tarski(B_107, C_106) | ~v2_tex_2(C_106, A_108) | ~m1_subset_1(C_106, k1_zfmisc_1(u1_struct_0(A_108))) | ~v3_tex_2(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.85/2.27  tff(c_612, plain, (![A_7, A_108]: (A_7='#skF_5' | ~v2_tex_2(A_7, A_108) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_108))) | ~v3_tex_2('#skF_5', A_108) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_72, c_610])).
% 4.85/2.27  tff(c_616, plain, (![A_109, A_110]: (A_109='#skF_5' | ~v2_tex_2(A_109, A_110) | ~m1_subset_1(A_109, k1_zfmisc_1(u1_struct_0(A_110))) | ~v3_tex_2('#skF_5', A_110) | ~l1_pre_topc(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_612])).
% 4.85/2.27  tff(c_912, plain, (![A_138, B_139]: (k6_domain_1(u1_struct_0(A_138), B_139)='#skF_5' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_138), B_139), A_138) | ~v3_tex_2('#skF_5', A_138) | ~l1_pre_topc(A_138) | ~m1_subset_1(B_139, u1_struct_0(A_138)) | v1_xboole_0(u1_struct_0(A_138)))), inference(resolution, [status(thm)], [c_26, c_616])).
% 4.85/2.27  tff(c_925, plain, (![A_140, B_141]: (k6_domain_1(u1_struct_0(A_140), B_141)='#skF_5' | ~v3_tex_2('#skF_5', A_140) | v1_xboole_0(u1_struct_0(A_140)) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_42, c_912])).
% 4.85/2.27  tff(c_966, plain, (![A_147]: (k6_domain_1(u1_struct_0(A_147), '#skF_1'('#skF_2'(u1_struct_0(A_147))))='#skF_5' | ~v3_tex_2('#skF_5', A_147) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | v1_xboole_0(u1_struct_0(A_147)) | v1_xboole_0('#skF_2'(u1_struct_0(A_147))))), inference(resolution, [status(thm)], [c_131, c_925])).
% 4.85/2.27  tff(c_155, plain, (![A_64]: (m1_subset_1('#skF_1'('#skF_2'(A_64)), A_64) | v1_xboole_0(A_64) | v1_xboole_0('#skF_2'(A_64)))), inference(resolution, [status(thm)], [c_4, c_126])).
% 4.85/2.27  tff(c_28, plain, (![A_20, B_21]: (k6_domain_1(A_20, B_21)=k1_tarski(B_21) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.85/2.27  tff(c_162, plain, (![A_64]: (k6_domain_1(A_64, '#skF_1'('#skF_2'(A_64)))=k1_tarski('#skF_1'('#skF_2'(A_64))) | v1_xboole_0(A_64) | v1_xboole_0('#skF_2'(A_64)))), inference(resolution, [status(thm)], [c_155, c_28])).
% 4.85/2.27  tff(c_987, plain, (![A_147]: (k1_tarski('#skF_1'('#skF_2'(u1_struct_0(A_147))))='#skF_5' | v1_xboole_0(u1_struct_0(A_147)) | v1_xboole_0('#skF_2'(u1_struct_0(A_147))) | ~v3_tex_2('#skF_5', A_147) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | v1_xboole_0(u1_struct_0(A_147)) | v1_xboole_0('#skF_2'(u1_struct_0(A_147))))), inference(superposition, [status(thm), theory('equality')], [c_966, c_162])).
% 4.85/2.27  tff(c_1004, plain, (![A_147]: (v1_xboole_0(u1_struct_0(A_147)) | v1_xboole_0('#skF_2'(u1_struct_0(A_147))) | ~v3_tex_2('#skF_5', A_147) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | v1_xboole_0(u1_struct_0(A_147)) | v1_xboole_0('#skF_2'(u1_struct_0(A_147))))), inference(negUnitSimplification, [status(thm)], [c_103, c_987])).
% 4.85/2.27  tff(c_1050, plain, (![A_151]: (~v3_tex_2('#skF_5', A_151) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151) | v1_xboole_0(u1_struct_0(A_151)) | v1_xboole_0('#skF_2'(u1_struct_0(A_151))))), inference(factorization, [status(thm), theory('equality')], [c_1004])).
% 4.85/2.27  tff(c_14, plain, (![A_10]: (~v1_xboole_0('#skF_2'(A_10)) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.85/2.27  tff(c_1059, plain, (![A_152]: (~v3_tex_2('#skF_5', A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152) | v1_xboole_0(u1_struct_0(A_152)))), inference(resolution, [status(thm)], [c_1050, c_14])).
% 4.85/2.27  tff(c_24, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.85/2.27  tff(c_1068, plain, (![A_153]: (~l1_struct_0(A_153) | ~v3_tex_2('#skF_5', A_153) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(resolution, [status(thm)], [c_1059, c_24])).
% 4.85/2.27  tff(c_1074, plain, (~l1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1068])).
% 4.85/2.27  tff(c_1078, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1074])).
% 4.85/2.27  tff(c_1079, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_1078])).
% 4.85/2.27  tff(c_1082, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1079])).
% 4.85/2.27  tff(c_1086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1082])).
% 4.85/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/2.27  
% 4.85/2.27  Inference rules
% 4.85/2.27  ----------------------
% 4.85/2.27  #Ref     : 0
% 4.85/2.27  #Sup     : 235
% 4.85/2.27  #Fact    : 2
% 4.85/2.27  #Define  : 0
% 4.85/2.27  #Split   : 2
% 4.85/2.27  #Chain   : 0
% 4.85/2.27  #Close   : 0
% 4.85/2.27  
% 4.85/2.27  Ordering : KBO
% 4.85/2.27  
% 4.85/2.27  Simplification rules
% 4.85/2.27  ----------------------
% 4.85/2.27  #Subsume      : 24
% 4.85/2.27  #Demod        : 38
% 4.85/2.27  #Tautology    : 44
% 4.85/2.27  #SimpNegUnit  : 7
% 4.85/2.27  #BackRed      : 7
% 4.85/2.27  
% 4.85/2.27  #Partial instantiations: 0
% 4.85/2.27  #Strategies tried      : 1
% 4.85/2.27  
% 4.85/2.27  Timing (in seconds)
% 4.85/2.27  ----------------------
% 4.85/2.27  Preprocessing        : 0.50
% 4.85/2.27  Parsing              : 0.26
% 4.85/2.27  CNF conversion       : 0.04
% 4.85/2.27  Main loop            : 0.86
% 4.85/2.27  Inferencing          : 0.32
% 4.85/2.27  Reduction            : 0.24
% 4.85/2.27  Demodulation         : 0.16
% 4.85/2.27  BG Simplification    : 0.05
% 4.85/2.27  Subsumption          : 0.18
% 4.85/2.27  Abstraction          : 0.04
% 4.85/2.27  MUC search           : 0.00
% 4.85/2.27  Cooper               : 0.00
% 4.85/2.28  Total                : 1.42
% 4.85/2.28  Index Insertion      : 0.00
% 4.85/2.28  Index Deletion       : 0.00
% 4.85/2.28  Index Matching       : 0.00
% 4.85/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
