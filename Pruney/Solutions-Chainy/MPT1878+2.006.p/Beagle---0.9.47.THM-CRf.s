%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:58 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 106 expanded)
%              Number of leaves         :   37 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 ( 231 expanded)
%              Number of equality atoms :   18 (  30 expanded)
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

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_101,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_128,plain,(
    ! [A_51,B_52] :
      ( k6_domain_1(A_51,B_52) = k1_tarski(B_52)
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_136,plain,(
    ! [A_6] :
      ( k6_domain_1(A_6,'#skF_1'(A_6)) = k1_tarski('#skF_1'(A_6))
      | v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_128])).

tff(c_297,plain,(
    ! [A_78,B_79] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_78),B_79),A_78)
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_301,plain,(
    ! [A_78] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_78))),A_78)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_78)),u1_struct_0(A_78))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | v1_xboole_0(u1_struct_0(A_78)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_297])).

tff(c_303,plain,(
    ! [A_78] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_78))),A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | v1_xboole_0(u1_struct_0(A_78)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_301])).

tff(c_46,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_54,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_54])).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_2] : k2_xboole_0(A_2,'#skF_5') = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4])).

tff(c_8,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),B_5) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,(
    ! [A_42,B_43] : k2_xboole_0(k1_tarski(A_42),B_43) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8])).

tff(c_91,plain,(
    ! [A_42] : k1_tarski(A_42) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_87])).

tff(c_176,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k6_domain_1(A_63,B_64),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_190,plain,(
    ! [A_6] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_6)),k1_zfmisc_1(A_6))
      | ~ m1_subset_1('#skF_1'(A_6),A_6)
      | v1_xboole_0(A_6)
      | v1_xboole_0(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_176])).

tff(c_197,plain,(
    ! [A_6] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_6)),k1_zfmisc_1(A_6))
      | v1_xboole_0(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_190])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6])).

tff(c_559,plain,(
    ! [C_113,B_114,A_115] :
      ( C_113 = B_114
      | ~ r1_tarski(B_114,C_113)
      | ~ v2_tex_2(C_113,A_115)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v3_tex_2(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_561,plain,(
    ! [A_3,A_115] :
      ( A_3 = '#skF_5'
      | ~ v2_tex_2(A_3,A_115)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v3_tex_2('#skF_5',A_115)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_60,c_559])).

tff(c_565,plain,(
    ! [A_116,A_117] :
      ( A_116 = '#skF_5'
      | ~ v2_tex_2(A_116,A_117)
      | ~ m1_subset_1(A_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ v3_tex_2('#skF_5',A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_561])).

tff(c_572,plain,(
    ! [A_117] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_117))) = '#skF_5'
      | ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_117))),A_117)
      | ~ v3_tex_2('#skF_5',A_117)
      | ~ l1_pre_topc(A_117)
      | v1_xboole_0(u1_struct_0(A_117)) ) ),
    inference(resolution,[status(thm)],[c_197,c_565])).

tff(c_597,plain,(
    ! [A_118] :
      ( ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_118))),A_118)
      | ~ v3_tex_2('#skF_5',A_118)
      | ~ l1_pre_topc(A_118)
      | v1_xboole_0(u1_struct_0(A_118)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_572])).

tff(c_602,plain,(
    ! [A_119] :
      ( ~ v3_tex_2('#skF_5',A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119)
      | v1_xboole_0(u1_struct_0(A_119)) ) ),
    inference(resolution,[status(thm)],[c_303,c_597])).

tff(c_198,plain,(
    ! [A_65] :
      ( m1_subset_1('#skF_2'(A_65),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [B_11,A_9] :
      ( v1_xboole_0(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_209,plain,(
    ! [A_65] :
      ( v1_xboole_0('#skF_2'(A_65))
      | ~ v1_xboole_0(u1_struct_0(A_65))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_198,c_14])).

tff(c_612,plain,(
    ! [A_121] :
      ( v1_xboole_0('#skF_2'(A_121))
      | ~ v3_tex_2('#skF_5',A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_602,c_209])).

tff(c_20,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0('#skF_2'(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_621,plain,(
    ! [A_122] :
      ( ~ v3_tex_2('#skF_5',A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_612,c_20])).

tff(c_627,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_621])).

tff(c_631,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_627])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:04:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.48  
% 2.96/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.49  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 2.96/1.49  
% 2.96/1.49  %Foreground sorts:
% 2.96/1.49  
% 2.96/1.49  
% 2.96/1.49  %Background operators:
% 2.96/1.49  
% 2.96/1.49  
% 2.96/1.49  %Foreground operators:
% 2.96/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.96/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.96/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.96/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.96/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.96/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.96/1.49  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.96/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.49  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.96/1.49  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.96/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.96/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.96/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.96/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.96/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.96/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.49  
% 3.05/1.50  tff(f_129, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 3.05/1.50  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.05/1.50  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.05/1.50  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 3.05/1.50  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.05/1.50  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.05/1.50  tff(f_36, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.05/1.50  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.05/1.50  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.05/1.50  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.05/1.50  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.05/1.50  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 3.05/1.50  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.05/1.50  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.05/1.50  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.05/1.50  tff(c_48, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.05/1.50  tff(c_42, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.05/1.50  tff(c_10, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.05/1.50  tff(c_128, plain, (![A_51, B_52]: (k6_domain_1(A_51, B_52)=k1_tarski(B_52) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.05/1.50  tff(c_136, plain, (![A_6]: (k6_domain_1(A_6, '#skF_1'(A_6))=k1_tarski('#skF_1'(A_6)) | v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_10, c_128])).
% 3.05/1.50  tff(c_297, plain, (![A_78, B_79]: (v2_tex_2(k6_domain_1(u1_struct_0(A_78), B_79), A_78) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.05/1.50  tff(c_301, plain, (![A_78]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_78))), A_78) | ~m1_subset_1('#skF_1'(u1_struct_0(A_78)), u1_struct_0(A_78)) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | v1_xboole_0(u1_struct_0(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_136, c_297])).
% 3.05/1.50  tff(c_303, plain, (![A_78]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_78))), A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | v1_xboole_0(u1_struct_0(A_78)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_301])).
% 3.05/1.50  tff(c_46, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.05/1.50  tff(c_54, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.05/1.50  tff(c_58, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_54])).
% 3.05/1.50  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.50  tff(c_67, plain, (![A_2]: (k2_xboole_0(A_2, '#skF_5')=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4])).
% 3.05/1.50  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.05/1.50  tff(c_87, plain, (![A_42, B_43]: (k2_xboole_0(k1_tarski(A_42), B_43)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8])).
% 3.05/1.50  tff(c_91, plain, (![A_42]: (k1_tarski(A_42)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_67, c_87])).
% 3.05/1.50  tff(c_176, plain, (![A_63, B_64]: (m1_subset_1(k6_domain_1(A_63, B_64), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.05/1.50  tff(c_190, plain, (![A_6]: (m1_subset_1(k1_tarski('#skF_1'(A_6)), k1_zfmisc_1(A_6)) | ~m1_subset_1('#skF_1'(A_6), A_6) | v1_xboole_0(A_6) | v1_xboole_0(A_6))), inference(superposition, [status(thm), theory('equality')], [c_136, c_176])).
% 3.05/1.50  tff(c_197, plain, (![A_6]: (m1_subset_1(k1_tarski('#skF_1'(A_6)), k1_zfmisc_1(A_6)) | v1_xboole_0(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_190])).
% 3.05/1.50  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.50  tff(c_77, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12])).
% 3.05/1.50  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.50  tff(c_60, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6])).
% 3.05/1.50  tff(c_559, plain, (![C_113, B_114, A_115]: (C_113=B_114 | ~r1_tarski(B_114, C_113) | ~v2_tex_2(C_113, A_115) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_115))) | ~v3_tex_2(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.05/1.50  tff(c_561, plain, (![A_3, A_115]: (A_3='#skF_5' | ~v2_tex_2(A_3, A_115) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_115))) | ~v3_tex_2('#skF_5', A_115) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_60, c_559])).
% 3.05/1.50  tff(c_565, plain, (![A_116, A_117]: (A_116='#skF_5' | ~v2_tex_2(A_116, A_117) | ~m1_subset_1(A_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~v3_tex_2('#skF_5', A_117) | ~l1_pre_topc(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_561])).
% 3.05/1.50  tff(c_572, plain, (![A_117]: (k1_tarski('#skF_1'(u1_struct_0(A_117)))='#skF_5' | ~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_117))), A_117) | ~v3_tex_2('#skF_5', A_117) | ~l1_pre_topc(A_117) | v1_xboole_0(u1_struct_0(A_117)))), inference(resolution, [status(thm)], [c_197, c_565])).
% 3.05/1.50  tff(c_597, plain, (![A_118]: (~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_118))), A_118) | ~v3_tex_2('#skF_5', A_118) | ~l1_pre_topc(A_118) | v1_xboole_0(u1_struct_0(A_118)))), inference(negUnitSimplification, [status(thm)], [c_91, c_572])).
% 3.05/1.50  tff(c_602, plain, (![A_119]: (~v3_tex_2('#skF_5', A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119) | v1_xboole_0(u1_struct_0(A_119)))), inference(resolution, [status(thm)], [c_303, c_597])).
% 3.05/1.50  tff(c_198, plain, (![A_65]: (m1_subset_1('#skF_2'(A_65), k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.05/1.50  tff(c_14, plain, (![B_11, A_9]: (v1_xboole_0(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.05/1.50  tff(c_209, plain, (![A_65]: (v1_xboole_0('#skF_2'(A_65)) | ~v1_xboole_0(u1_struct_0(A_65)) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_198, c_14])).
% 3.05/1.50  tff(c_612, plain, (![A_121]: (v1_xboole_0('#skF_2'(A_121)) | ~v3_tex_2('#skF_5', A_121) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_602, c_209])).
% 3.05/1.50  tff(c_20, plain, (![A_15]: (~v1_xboole_0('#skF_2'(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.05/1.50  tff(c_621, plain, (![A_122]: (~v3_tex_2('#skF_5', A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(resolution, [status(thm)], [c_612, c_20])).
% 3.05/1.50  tff(c_627, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_621])).
% 3.05/1.50  tff(c_631, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_627])).
% 3.05/1.50  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_631])).
% 3.05/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.50  
% 3.05/1.50  Inference rules
% 3.05/1.50  ----------------------
% 3.05/1.50  #Ref     : 0
% 3.05/1.50  #Sup     : 132
% 3.05/1.50  #Fact    : 0
% 3.05/1.50  #Define  : 0
% 3.05/1.50  #Split   : 0
% 3.05/1.50  #Chain   : 0
% 3.05/1.50  #Close   : 0
% 3.05/1.50  
% 3.05/1.50  Ordering : KBO
% 3.05/1.50  
% 3.05/1.50  Simplification rules
% 3.05/1.50  ----------------------
% 3.05/1.50  #Subsume      : 16
% 3.05/1.50  #Demod        : 21
% 3.05/1.50  #Tautology    : 30
% 3.05/1.50  #SimpNegUnit  : 2
% 3.05/1.50  #BackRed      : 2
% 3.05/1.50  
% 3.05/1.50  #Partial instantiations: 0
% 3.05/1.50  #Strategies tried      : 1
% 3.05/1.50  
% 3.05/1.50  Timing (in seconds)
% 3.05/1.50  ----------------------
% 3.05/1.50  Preprocessing        : 0.33
% 3.05/1.51  Parsing              : 0.18
% 3.05/1.51  CNF conversion       : 0.02
% 3.05/1.51  Main loop            : 0.34
% 3.05/1.51  Inferencing          : 0.13
% 3.05/1.51  Reduction            : 0.09
% 3.05/1.51  Demodulation         : 0.06
% 3.05/1.51  BG Simplification    : 0.02
% 3.05/1.51  Subsumption          : 0.06
% 3.05/1.51  Abstraction          : 0.02
% 3.05/1.51  MUC search           : 0.00
% 3.05/1.51  Cooper               : 0.00
% 3.05/1.51  Total                : 0.70
% 3.05/1.51  Index Insertion      : 0.00
% 3.05/1.51  Index Deletion       : 0.00
% 3.05/1.51  Index Matching       : 0.00
% 3.05/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
