%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1878+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:37 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 106 expanded)
%              Number of leaves         :   37 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  152 ( 231 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_76,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_71,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_20,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_44,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_104,plain,(
    ! [A_44] :
      ( v1_xboole_0(A_44)
      | r2_hidden('#skF_1'(A_44),A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_111,plain,(
    ! [A_44] :
      ( m1_subset_1('#skF_1'(A_44),A_44)
      | v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_104,c_34])).

tff(c_36,plain,(
    ! [A_26,B_28] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_26),B_28),A_26)
      | ~ m1_subset_1(B_28,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k6_domain_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_57,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_57])).

tff(c_28,plain,(
    ! [A_20] : v1_xboole_0('#skF_3'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_67,plain,(
    ! [A_20] : '#skF_3'(A_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_57])).

tff(c_82,plain,(
    ! [A_20] : '#skF_3'(A_20) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_67])).

tff(c_30,plain,(
    ! [A_20] : m1_subset_1('#skF_3'(A_20),k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_99,plain,(
    ! [A_20] : m1_subset_1('#skF_5',k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_30])).

tff(c_116,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_129,plain,(
    ! [A_20] : r1_tarski('#skF_5',A_20) ),
    inference(resolution,[status(thm)],[c_99,c_116])).

tff(c_545,plain,(
    ! [C_100,B_101,A_102] :
      ( C_100 = B_101
      | ~ r1_tarski(B_101,C_100)
      | ~ v2_tex_2(C_100,A_102)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v3_tex_2(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_559,plain,(
    ! [A_20,A_102] :
      ( A_20 = '#skF_5'
      | ~ v2_tex_2(A_20,A_102)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v3_tex_2('#skF_5',A_102)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_129,c_545])).

tff(c_569,plain,(
    ! [A_103,A_104] :
      ( A_103 = '#skF_5'
      | ~ v2_tex_2(A_103,A_104)
      | ~ m1_subset_1(A_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ v3_tex_2('#skF_5',A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_559])).

tff(c_965,plain,(
    ! [A_128,B_129] :
      ( k6_domain_1(u1_struct_0(A_128),B_129) = '#skF_5'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_128),B_129),A_128)
      | ~ v3_tex_2('#skF_5',A_128)
      | ~ l1_pre_topc(A_128)
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | v1_xboole_0(u1_struct_0(A_128)) ) ),
    inference(resolution,[status(thm)],[c_18,c_569])).

tff(c_974,plain,(
    ! [A_130,B_131] :
      ( k6_domain_1(u1_struct_0(A_130),B_131) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_130)
      | v1_xboole_0(u1_struct_0(A_130))
      | ~ m1_subset_1(B_131,u1_struct_0(A_130))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_36,c_965])).

tff(c_980,plain,(
    ! [A_132] :
      ( k6_domain_1(u1_struct_0(A_132),'#skF_1'(u1_struct_0(A_132))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_132)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132)
      | v1_xboole_0(u1_struct_0(A_132)) ) ),
    inference(resolution,[status(thm)],[c_111,c_974])).

tff(c_132,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_143,plain,(
    ! [A_44] :
      ( k6_domain_1(A_44,'#skF_1'(A_44)) = k1_tarski('#skF_1'(A_44))
      | v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_111,c_132])).

tff(c_1015,plain,(
    ! [A_133] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_133))) = '#skF_5'
      | v1_xboole_0(u1_struct_0(A_133))
      | ~ v3_tex_2('#skF_5',A_133)
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133)
      | v1_xboole_0(u1_struct_0(A_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_143])).

tff(c_26,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_tarski(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1053,plain,(
    ! [A_133] :
      ( ~ v1_xboole_0('#skF_5')
      | v1_xboole_0(u1_struct_0(A_133))
      | ~ v3_tex_2('#skF_5',A_133)
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133)
      | v1_xboole_0(u1_struct_0(A_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1015,c_26])).

tff(c_1067,plain,(
    ! [A_134] :
      ( ~ v3_tex_2('#skF_5',A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | v1_xboole_0(u1_struct_0(A_134)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1053])).

tff(c_24,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1076,plain,(
    ! [A_135] :
      ( ~ l1_struct_0(A_135)
      | ~ v3_tex_2('#skF_5',A_135)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_1067,c_24])).

tff(c_1082,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1076])).

tff(c_1086,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1082])).

tff(c_1087,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1086])).

tff(c_1090,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1087])).

tff(c_1094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1090])).

%------------------------------------------------------------------------------
