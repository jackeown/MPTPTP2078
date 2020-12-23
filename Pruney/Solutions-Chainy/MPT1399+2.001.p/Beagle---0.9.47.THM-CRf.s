%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:18 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 550 expanded)
%              Number of leaves         :   55 ( 208 expanded)
%              Depth                    :   17
%              Number of atoms          :  254 (1318 expanded)
%              Number of equality atoms :   51 ( 363 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_242,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_109,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_111,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_179,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_168,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_205,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_214,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_196,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_104,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_102,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_100,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_46,plain,(
    ! [A_36] : v1_xboole_0('#skF_2'(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_94,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_30,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_147,plain,(
    ! [A_92] :
      ( A_92 = '#skF_7'
      | ~ v1_xboole_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_30])).

tff(c_151,plain,(
    ! [A_36] : '#skF_2'(A_36) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_46,c_147])).

tff(c_152,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_46])).

tff(c_50,plain,(
    ! [A_38] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_116,plain,(
    ! [A_38] : m1_subset_1('#skF_7',k1_zfmisc_1(A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_50])).

tff(c_2057,plain,(
    ! [B_218,A_219] :
      ( v3_pre_topc(B_218,A_219)
      | ~ v1_xboole_0(B_218)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2080,plain,(
    ! [A_219] :
      ( v3_pre_topc('#skF_7',A_219)
      | ~ v1_xboole_0('#skF_7')
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219) ) ),
    inference(resolution,[status(thm)],[c_116,c_2057])).

tff(c_2088,plain,(
    ! [A_219] :
      ( v3_pre_topc('#skF_7',A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_2080])).

tff(c_2737,plain,(
    ! [B_247,A_248] :
      ( v4_pre_topc(B_247,A_248)
      | ~ v1_xboole_0(B_247)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_2760,plain,(
    ! [A_248] :
      ( v4_pre_topc('#skF_7',A_248)
      | ~ v1_xboole_0('#skF_7')
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248) ) ),
    inference(resolution,[status(thm)],[c_116,c_2737])).

tff(c_2768,plain,(
    ! [A_248] :
      ( v4_pre_topc('#skF_7',A_248)
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_2760])).

tff(c_98,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_395,plain,(
    ! [B_110,A_111] :
      ( v1_xboole_0(B_110)
      | ~ m1_subset_1(B_110,A_111)
      | ~ v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_404,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_98,c_395])).

tff(c_405,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_214,plain,(
    ! [B_100,A_101] : k2_xboole_0(B_100,A_101) = k2_xboole_0(A_101,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_122,plain,(
    ! [A_10] : k2_xboole_0(A_10,'#skF_7') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_10])).

tff(c_230,plain,(
    ! [A_101] : k2_xboole_0('#skF_7',A_101) = A_101 ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_122])).

tff(c_305,plain,(
    ! [A_105,B_106] : k2_xboole_0(A_105,k3_xboole_0(A_105,B_106)) = A_105 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_319,plain,(
    ! [B_106] : k3_xboole_0('#skF_7',B_106) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_305])).

tff(c_545,plain,(
    ! [A_129,B_130] : k4_xboole_0(A_129,k4_xboole_0(A_129,B_130)) = k3_xboole_0(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_461,plain,(
    ! [A_121,B_122] : k4_xboole_0(A_121,k3_xboole_0(A_121,B_122)) = k4_xboole_0(A_121,B_122) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_470,plain,(
    ! [B_106] : k4_xboole_0('#skF_7',B_106) = k4_xboole_0('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_461])).

tff(c_485,plain,(
    ! [B_125] : k4_xboole_0('#skF_7',B_125) = k4_xboole_0('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_461])).

tff(c_493,plain,(
    ! [B_125,B_106] : k4_xboole_0('#skF_7',B_125) = k4_xboole_0('#skF_7',B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_485])).

tff(c_555,plain,(
    ! [B_106,B_130] : k4_xboole_0('#skF_7',B_106) = k3_xboole_0('#skF_7',B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_493])).

tff(c_585,plain,(
    ! [B_106] : k4_xboole_0('#skF_7',B_106) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_555])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_562,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,k4_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_545])).

tff(c_656,plain,(
    ! [A_138,B_139] : k3_xboole_0(A_138,k4_xboole_0(A_138,B_139)) = k4_xboole_0(A_138,B_139) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_562])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_672,plain,(
    ! [A_138,B_139] : k2_xboole_0(A_138,k4_xboole_0(A_138,B_139)) = A_138 ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1474,plain,(
    ! [A_192,B_193,C_194] : k2_xboole_0(k4_xboole_0(A_192,B_193),k3_xboole_0(A_192,C_194)) = k4_xboole_0(A_192,k4_xboole_0(B_193,C_194)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1531,plain,(
    ! [A_3,B_193] : k4_xboole_0(A_3,k4_xboole_0(B_193,A_3)) = k2_xboole_0(k4_xboole_0(A_3,B_193),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1474])).

tff(c_1544,plain,(
    ! [A_195,B_196] : k4_xboole_0(A_195,k4_xboole_0(B_196,A_195)) = A_195 ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_2,c_1531])).

tff(c_1601,plain,(
    ! [B_106] : k4_xboole_0(B_106,'#skF_7') = B_106 ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_1544])).

tff(c_817,plain,(
    ! [A_151,B_152] :
      ( k4_xboole_0(A_151,B_152) = k3_subset_1(A_151,B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_830,plain,(
    ! [A_38] : k4_xboole_0(A_38,'#skF_7') = k3_subset_1(A_38,'#skF_7') ),
    inference(resolution,[status(thm)],[c_116,c_817])).

tff(c_1628,plain,(
    ! [A_38] : k3_subset_1(A_38,'#skF_7') = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1601,c_830])).

tff(c_36,plain,(
    ! [B_31,A_30] :
      ( r2_hidden(B_31,A_30)
      | ~ m1_subset_1(B_31,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_88,plain,(
    ! [A_70,B_72] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_70),B_72),A_70)
      | ~ v4_pre_topc(B_72,A_70)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_3744,plain,(
    ! [A_271,B_272] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_271),B_272),A_271)
      | ~ v3_pre_topc(B_272,A_271)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_786,plain,(
    ! [A_146,B_147] :
      ( m1_subset_1(k3_subset_1(A_146,B_147),k1_zfmisc_1(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_14])).

tff(c_438,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,k3_xboole_0(A_117,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_448,plain,(
    ! [A_13,C_119] :
      ( ~ r1_xboole_0(A_13,'#skF_7')
      | ~ r2_hidden(C_119,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_438])).

tff(c_453,plain,(
    ! [C_119] : ~ r2_hidden(C_119,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_106,plain,(
    ! [D_87] :
      ( r2_hidden(D_87,'#skF_7')
      | ~ r2_hidden('#skF_6',D_87)
      | ~ v4_pre_topc(D_87,'#skF_5')
      | ~ v3_pre_topc(D_87,'#skF_5')
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_500,plain,(
    ! [D_87] :
      ( ~ r2_hidden('#skF_6',D_87)
      | ~ v4_pre_topc(D_87,'#skF_5')
      | ~ v3_pre_topc(D_87,'#skF_5')
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_453,c_106])).

tff(c_798,plain,(
    ! [B_147] :
      ( ~ r2_hidden('#skF_6',k3_subset_1(u1_struct_0('#skF_5'),B_147))
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_5'),B_147),'#skF_5')
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_5'),B_147),'#skF_5')
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_786,c_500])).

tff(c_3748,plain,(
    ! [B_272] :
      ( ~ r2_hidden('#skF_6',k3_subset_1(u1_struct_0('#skF_5'),B_272))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_5'),B_272),'#skF_5')
      | ~ v3_pre_topc(B_272,'#skF_5')
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3744,c_798])).

tff(c_4314,plain,(
    ! [B_293] :
      ( ~ r2_hidden('#skF_6',k3_subset_1(u1_struct_0('#skF_5'),B_293))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_5'),B_293),'#skF_5')
      | ~ v3_pre_topc(B_293,'#skF_5')
      | ~ m1_subset_1(B_293,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_3748])).

tff(c_4318,plain,(
    ! [B_72] :
      ( ~ r2_hidden('#skF_6',k3_subset_1(u1_struct_0('#skF_5'),B_72))
      | ~ v3_pre_topc(B_72,'#skF_5')
      | ~ v4_pre_topc(B_72,'#skF_5')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_88,c_4314])).

tff(c_5037,plain,(
    ! [B_307] :
      ( ~ r2_hidden('#skF_6',k3_subset_1(u1_struct_0('#skF_5'),B_307))
      | ~ v3_pre_topc(B_307,'#skF_5')
      | ~ v4_pre_topc(B_307,'#skF_5')
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_4318])).

tff(c_6227,plain,(
    ! [B_324] :
      ( ~ v3_pre_topc(B_324,'#skF_5')
      | ~ v4_pre_topc(B_324,'#skF_5')
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k3_subset_1(u1_struct_0('#skF_5'),B_324))
      | v1_xboole_0(k3_subset_1(u1_struct_0('#skF_5'),B_324)) ) ),
    inference(resolution,[status(thm)],[c_36,c_5037])).

tff(c_6245,plain,
    ( ~ v3_pre_topc('#skF_7','#skF_5')
    | ~ v4_pre_topc('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_6',k3_subset_1(u1_struct_0('#skF_5'),'#skF_7'))
    | v1_xboole_0(k3_subset_1(u1_struct_0('#skF_5'),'#skF_7')) ),
    inference(resolution,[status(thm)],[c_116,c_6227])).

tff(c_6258,plain,
    ( ~ v3_pre_topc('#skF_7','#skF_5')
    | ~ v4_pre_topc('#skF_7','#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1628,c_98,c_1628,c_6245])).

tff(c_6259,plain,
    ( ~ v3_pre_topc('#skF_7','#skF_5')
    | ~ v4_pre_topc('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_6258])).

tff(c_6260,plain,(
    ~ v4_pre_topc('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6259])).

tff(c_6263,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2768,c_6260])).

tff(c_6267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_6263])).

tff(c_6268,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_6259])).

tff(c_6272,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2088,c_6268])).

tff(c_6276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_6272])).

tff(c_6277,plain,(
    ! [A_13] : ~ r1_xboole_0(A_13,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_26,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_120,plain,(
    r1_xboole_0('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_26])).

tff(c_6279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6277,c_120])).

tff(c_6280,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_6281,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_118,plain,(
    ! [A_27] :
      ( A_27 = '#skF_7'
      | ~ v1_xboole_0(A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_30])).

tff(c_6303,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6280,c_118])).

tff(c_6397,plain,(
    ! [A_332] :
      ( A_332 = '#skF_6'
      | ~ v1_xboole_0(A_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6303,c_118])).

tff(c_6404,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6281,c_6397])).

tff(c_7456,plain,(
    ! [A_411] :
      ( m1_subset_1('#skF_4'(A_411),k1_zfmisc_1(u1_struct_0(A_411)))
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_7473,plain,
    ( m1_subset_1('#skF_4'('#skF_5'),k1_zfmisc_1('#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6404,c_7456])).

tff(c_7480,plain,
    ( m1_subset_1('#skF_4'('#skF_5'),k1_zfmisc_1('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_7473])).

tff(c_7481,plain,(
    m1_subset_1('#skF_4'('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_7480])).

tff(c_52,plain,(
    ! [B_41,A_39] :
      ( v1_xboole_0(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7492,plain,
    ( v1_xboole_0('#skF_4'('#skF_5'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_7481,c_52])).

tff(c_7504,plain,(
    v1_xboole_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6280,c_7492])).

tff(c_82,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0('#skF_4'(A_68))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_7513,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_7504,c_82])).

tff(c_7523,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_7513])).

tff(c_7525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_7523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:20:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.12  
% 5.75/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.75/2.13  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 5.75/2.13  
% 5.75/2.13  %Foreground sorts:
% 5.75/2.13  
% 5.75/2.13  
% 5.75/2.13  %Background operators:
% 5.75/2.13  
% 5.75/2.13  
% 5.75/2.13  %Foreground operators:
% 5.75/2.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.75/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.13  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.75/2.13  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.75/2.13  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.75/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.75/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.75/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.75/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.13  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.75/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.75/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.75/2.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.75/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.75/2.13  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.75/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.13  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.75/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.75/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.75/2.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.75/2.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.75/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.75/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.13  
% 5.84/2.15  tff(f_242, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 5.84/2.15  tff(f_109, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 5.84/2.15  tff(f_75, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 5.84/2.15  tff(f_111, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.84/2.15  tff(f_179, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 5.84/2.15  tff(f_168, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 5.84/2.15  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.84/2.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.84/2.15  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.84/2.15  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.84/2.15  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.84/2.15  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.84/2.15  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.84/2.15  tff(f_57, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 5.84/2.15  tff(f_100, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.84/2.15  tff(f_205, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 5.84/2.15  tff(f_214, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 5.84/2.15  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.84/2.15  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.84/2.15  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.84/2.15  tff(f_71, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 5.84/2.15  tff(f_196, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 5.84/2.15  tff(f_118, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.84/2.15  tff(c_104, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.84/2.15  tff(c_102, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.84/2.15  tff(c_100, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.84/2.15  tff(c_46, plain, (![A_36]: (v1_xboole_0('#skF_2'(A_36)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.84/2.15  tff(c_94, plain, (k1_xboole_0='#skF_7'), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.84/2.15  tff(c_30, plain, (![A_27]: (k1_xboole_0=A_27 | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.84/2.15  tff(c_147, plain, (![A_92]: (A_92='#skF_7' | ~v1_xboole_0(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_30])).
% 5.84/2.15  tff(c_151, plain, (![A_36]: ('#skF_2'(A_36)='#skF_7')), inference(resolution, [status(thm)], [c_46, c_147])).
% 5.84/2.15  tff(c_152, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_46])).
% 5.84/2.15  tff(c_50, plain, (![A_38]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.84/2.15  tff(c_116, plain, (![A_38]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_50])).
% 5.84/2.15  tff(c_2057, plain, (![B_218, A_219]: (v3_pre_topc(B_218, A_219) | ~v1_xboole_0(B_218) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.84/2.15  tff(c_2080, plain, (![A_219]: (v3_pre_topc('#skF_7', A_219) | ~v1_xboole_0('#skF_7') | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219))), inference(resolution, [status(thm)], [c_116, c_2057])).
% 5.84/2.15  tff(c_2088, plain, (![A_219]: (v3_pre_topc('#skF_7', A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_2080])).
% 5.84/2.15  tff(c_2737, plain, (![B_247, A_248]: (v4_pre_topc(B_247, A_248) | ~v1_xboole_0(B_247) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248))), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.84/2.15  tff(c_2760, plain, (![A_248]: (v4_pre_topc('#skF_7', A_248) | ~v1_xboole_0('#skF_7') | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248))), inference(resolution, [status(thm)], [c_116, c_2737])).
% 5.84/2.15  tff(c_2768, plain, (![A_248]: (v4_pre_topc('#skF_7', A_248) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_2760])).
% 5.84/2.15  tff(c_98, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.84/2.15  tff(c_395, plain, (![B_110, A_111]: (v1_xboole_0(B_110) | ~m1_subset_1(B_110, A_111) | ~v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.84/2.15  tff(c_404, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_98, c_395])).
% 5.84/2.15  tff(c_405, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_404])).
% 5.84/2.15  tff(c_214, plain, (![B_100, A_101]: (k2_xboole_0(B_100, A_101)=k2_xboole_0(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.84/2.15  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.84/2.15  tff(c_122, plain, (![A_10]: (k2_xboole_0(A_10, '#skF_7')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_10])).
% 5.84/2.15  tff(c_230, plain, (![A_101]: (k2_xboole_0('#skF_7', A_101)=A_101)), inference(superposition, [status(thm), theory('equality')], [c_214, c_122])).
% 5.84/2.15  tff(c_305, plain, (![A_105, B_106]: (k2_xboole_0(A_105, k3_xboole_0(A_105, B_106))=A_105)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.84/2.15  tff(c_319, plain, (![B_106]: (k3_xboole_0('#skF_7', B_106)='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_230, c_305])).
% 5.84/2.15  tff(c_545, plain, (![A_129, B_130]: (k4_xboole_0(A_129, k4_xboole_0(A_129, B_130))=k3_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.84/2.15  tff(c_461, plain, (![A_121, B_122]: (k4_xboole_0(A_121, k3_xboole_0(A_121, B_122))=k4_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.84/2.15  tff(c_470, plain, (![B_106]: (k4_xboole_0('#skF_7', B_106)=k4_xboole_0('#skF_7', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_461])).
% 5.84/2.15  tff(c_485, plain, (![B_125]: (k4_xboole_0('#skF_7', B_125)=k4_xboole_0('#skF_7', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_461])).
% 5.84/2.15  tff(c_493, plain, (![B_125, B_106]: (k4_xboole_0('#skF_7', B_125)=k4_xboole_0('#skF_7', B_106))), inference(superposition, [status(thm), theory('equality')], [c_470, c_485])).
% 5.84/2.15  tff(c_555, plain, (![B_106, B_130]: (k4_xboole_0('#skF_7', B_106)=k3_xboole_0('#skF_7', B_130))), inference(superposition, [status(thm), theory('equality')], [c_545, c_493])).
% 5.84/2.15  tff(c_585, plain, (![B_106]: (k4_xboole_0('#skF_7', B_106)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_555])).
% 5.84/2.15  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.84/2.15  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.84/2.15  tff(c_562, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k3_xboole_0(A_16, k4_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_545])).
% 5.84/2.15  tff(c_656, plain, (![A_138, B_139]: (k3_xboole_0(A_138, k4_xboole_0(A_138, B_139))=k4_xboole_0(A_138, B_139))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_562])).
% 5.84/2.15  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k3_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.84/2.15  tff(c_672, plain, (![A_138, B_139]: (k2_xboole_0(A_138, k4_xboole_0(A_138, B_139))=A_138)), inference(superposition, [status(thm), theory('equality')], [c_656, c_12])).
% 5.84/2.15  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.84/2.15  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.84/2.15  tff(c_1474, plain, (![A_192, B_193, C_194]: (k2_xboole_0(k4_xboole_0(A_192, B_193), k3_xboole_0(A_192, C_194))=k4_xboole_0(A_192, k4_xboole_0(B_193, C_194)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.84/2.15  tff(c_1531, plain, (![A_3, B_193]: (k4_xboole_0(A_3, k4_xboole_0(B_193, A_3))=k2_xboole_0(k4_xboole_0(A_3, B_193), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1474])).
% 5.84/2.15  tff(c_1544, plain, (![A_195, B_196]: (k4_xboole_0(A_195, k4_xboole_0(B_196, A_195))=A_195)), inference(demodulation, [status(thm), theory('equality')], [c_672, c_2, c_1531])).
% 5.84/2.15  tff(c_1601, plain, (![B_106]: (k4_xboole_0(B_106, '#skF_7')=B_106)), inference(superposition, [status(thm), theory('equality')], [c_585, c_1544])).
% 5.84/2.15  tff(c_817, plain, (![A_151, B_152]: (k4_xboole_0(A_151, B_152)=k3_subset_1(A_151, B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.84/2.15  tff(c_830, plain, (![A_38]: (k4_xboole_0(A_38, '#skF_7')=k3_subset_1(A_38, '#skF_7'))), inference(resolution, [status(thm)], [c_116, c_817])).
% 5.84/2.15  tff(c_1628, plain, (![A_38]: (k3_subset_1(A_38, '#skF_7')=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_1601, c_830])).
% 5.84/2.15  tff(c_36, plain, (![B_31, A_30]: (r2_hidden(B_31, A_30) | ~m1_subset_1(B_31, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.84/2.15  tff(c_88, plain, (![A_70, B_72]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_70), B_72), A_70) | ~v4_pre_topc(B_72, A_70) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.84/2.15  tff(c_3744, plain, (![A_271, B_272]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_271), B_272), A_271) | ~v3_pre_topc(B_272, A_271) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_214])).
% 5.84/2.15  tff(c_786, plain, (![A_146, B_147]: (m1_subset_1(k3_subset_1(A_146, B_147), k1_zfmisc_1(A_146)) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.84/2.15  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.84/2.15  tff(c_121, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_14])).
% 5.84/2.15  tff(c_438, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, k3_xboole_0(A_117, B_118)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.84/2.15  tff(c_448, plain, (![A_13, C_119]: (~r1_xboole_0(A_13, '#skF_7') | ~r2_hidden(C_119, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_438])).
% 5.84/2.15  tff(c_453, plain, (![C_119]: (~r2_hidden(C_119, '#skF_7'))), inference(splitLeft, [status(thm)], [c_448])).
% 5.84/2.15  tff(c_106, plain, (![D_87]: (r2_hidden(D_87, '#skF_7') | ~r2_hidden('#skF_6', D_87) | ~v4_pre_topc(D_87, '#skF_5') | ~v3_pre_topc(D_87, '#skF_5') | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.84/2.15  tff(c_500, plain, (![D_87]: (~r2_hidden('#skF_6', D_87) | ~v4_pre_topc(D_87, '#skF_5') | ~v3_pre_topc(D_87, '#skF_5') | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_453, c_106])).
% 5.84/2.15  tff(c_798, plain, (![B_147]: (~r2_hidden('#skF_6', k3_subset_1(u1_struct_0('#skF_5'), B_147)) | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_5'), B_147), '#skF_5') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_5'), B_147), '#skF_5') | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_786, c_500])).
% 5.84/2.15  tff(c_3748, plain, (![B_272]: (~r2_hidden('#skF_6', k3_subset_1(u1_struct_0('#skF_5'), B_272)) | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_5'), B_272), '#skF_5') | ~v3_pre_topc(B_272, '#skF_5') | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_3744, c_798])).
% 5.84/2.15  tff(c_4314, plain, (![B_293]: (~r2_hidden('#skF_6', k3_subset_1(u1_struct_0('#skF_5'), B_293)) | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_5'), B_293), '#skF_5') | ~v3_pre_topc(B_293, '#skF_5') | ~m1_subset_1(B_293, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_3748])).
% 5.84/2.15  tff(c_4318, plain, (![B_72]: (~r2_hidden('#skF_6', k3_subset_1(u1_struct_0('#skF_5'), B_72)) | ~v3_pre_topc(B_72, '#skF_5') | ~v4_pre_topc(B_72, '#skF_5') | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_88, c_4314])).
% 5.84/2.15  tff(c_5037, plain, (![B_307]: (~r2_hidden('#skF_6', k3_subset_1(u1_struct_0('#skF_5'), B_307)) | ~v3_pre_topc(B_307, '#skF_5') | ~v4_pre_topc(B_307, '#skF_5') | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_4318])).
% 5.84/2.15  tff(c_6227, plain, (![B_324]: (~v3_pre_topc(B_324, '#skF_5') | ~v4_pre_topc(B_324, '#skF_5') | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k3_subset_1(u1_struct_0('#skF_5'), B_324)) | v1_xboole_0(k3_subset_1(u1_struct_0('#skF_5'), B_324)))), inference(resolution, [status(thm)], [c_36, c_5037])).
% 5.84/2.15  tff(c_6245, plain, (~v3_pre_topc('#skF_7', '#skF_5') | ~v4_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_6', k3_subset_1(u1_struct_0('#skF_5'), '#skF_7')) | v1_xboole_0(k3_subset_1(u1_struct_0('#skF_5'), '#skF_7'))), inference(resolution, [status(thm)], [c_116, c_6227])).
% 5.84/2.15  tff(c_6258, plain, (~v3_pre_topc('#skF_7', '#skF_5') | ~v4_pre_topc('#skF_7', '#skF_5') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1628, c_98, c_1628, c_6245])).
% 5.84/2.15  tff(c_6259, plain, (~v3_pre_topc('#skF_7', '#skF_5') | ~v4_pre_topc('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_405, c_6258])).
% 5.84/2.15  tff(c_6260, plain, (~v4_pre_topc('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_6259])).
% 5.84/2.15  tff(c_6263, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2768, c_6260])).
% 5.84/2.15  tff(c_6267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_6263])).
% 5.84/2.15  tff(c_6268, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_6259])).
% 5.84/2.15  tff(c_6272, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2088, c_6268])).
% 5.84/2.15  tff(c_6276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_6272])).
% 5.84/2.15  tff(c_6277, plain, (![A_13]: (~r1_xboole_0(A_13, '#skF_7'))), inference(splitRight, [status(thm)], [c_448])).
% 5.84/2.15  tff(c_26, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.84/2.15  tff(c_120, plain, (r1_xboole_0('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_26])).
% 5.84/2.15  tff(c_6279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6277, c_120])).
% 5.84/2.15  tff(c_6280, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_404])).
% 5.84/2.15  tff(c_6281, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_404])).
% 5.84/2.15  tff(c_118, plain, (![A_27]: (A_27='#skF_7' | ~v1_xboole_0(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_30])).
% 5.84/2.15  tff(c_6303, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_6280, c_118])).
% 5.84/2.15  tff(c_6397, plain, (![A_332]: (A_332='#skF_6' | ~v1_xboole_0(A_332))), inference(demodulation, [status(thm), theory('equality')], [c_6303, c_118])).
% 5.84/2.15  tff(c_6404, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_6281, c_6397])).
% 5.84/2.15  tff(c_7456, plain, (![A_411]: (m1_subset_1('#skF_4'(A_411), k1_zfmisc_1(u1_struct_0(A_411))) | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.84/2.15  tff(c_7473, plain, (m1_subset_1('#skF_4'('#skF_5'), k1_zfmisc_1('#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6404, c_7456])).
% 5.84/2.15  tff(c_7480, plain, (m1_subset_1('#skF_4'('#skF_5'), k1_zfmisc_1('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_7473])).
% 5.84/2.15  tff(c_7481, plain, (m1_subset_1('#skF_4'('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_104, c_7480])).
% 5.84/2.15  tff(c_52, plain, (![B_41, A_39]: (v1_xboole_0(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.84/2.15  tff(c_7492, plain, (v1_xboole_0('#skF_4'('#skF_5')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_7481, c_52])).
% 5.84/2.15  tff(c_7504, plain, (v1_xboole_0('#skF_4'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6280, c_7492])).
% 5.84/2.15  tff(c_82, plain, (![A_68]: (~v1_xboole_0('#skF_4'(A_68)) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.84/2.15  tff(c_7513, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_7504, c_82])).
% 5.84/2.15  tff(c_7523, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_7513])).
% 5.84/2.15  tff(c_7525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_7523])).
% 5.84/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.84/2.15  
% 5.84/2.15  Inference rules
% 5.84/2.15  ----------------------
% 5.84/2.15  #Ref     : 0
% 5.84/2.15  #Sup     : 1783
% 5.84/2.15  #Fact    : 0
% 5.84/2.15  #Define  : 0
% 5.84/2.15  #Split   : 11
% 5.84/2.15  #Chain   : 0
% 5.84/2.15  #Close   : 0
% 5.84/2.15  
% 5.84/2.15  Ordering : KBO
% 5.84/2.15  
% 5.84/2.15  Simplification rules
% 5.84/2.15  ----------------------
% 5.84/2.15  #Subsume      : 112
% 5.84/2.15  #Demod        : 1618
% 5.84/2.15  #Tautology    : 1129
% 5.84/2.15  #SimpNegUnit  : 20
% 5.84/2.15  #BackRed      : 33
% 5.84/2.15  
% 5.84/2.15  #Partial instantiations: 0
% 5.84/2.15  #Strategies tried      : 1
% 5.84/2.15  
% 5.84/2.15  Timing (in seconds)
% 5.84/2.15  ----------------------
% 5.84/2.15  Preprocessing        : 0.38
% 5.84/2.15  Parsing              : 0.20
% 5.84/2.15  CNF conversion       : 0.03
% 5.84/2.15  Main loop            : 0.99
% 5.84/2.15  Inferencing          : 0.31
% 5.84/2.15  Reduction            : 0.40
% 5.84/2.15  Demodulation         : 0.31
% 5.84/2.15  BG Simplification    : 0.04
% 5.84/2.15  Subsumption          : 0.17
% 5.84/2.15  Abstraction          : 0.05
% 5.84/2.15  MUC search           : 0.00
% 5.84/2.15  Cooper               : 0.00
% 5.84/2.15  Total                : 1.42
% 5.84/2.15  Index Insertion      : 0.00
% 5.84/2.15  Index Deletion       : 0.00
% 5.84/2.15  Index Matching       : 0.00
% 5.84/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
