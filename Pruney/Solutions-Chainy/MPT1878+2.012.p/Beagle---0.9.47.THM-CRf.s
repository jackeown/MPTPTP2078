%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:59 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 103 expanded)
%              Number of leaves         :   38 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 231 expanded)
%              Number of equality atoms :   18 (  27 expanded)
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

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_104,axiom,(
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

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_150,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_162,plain,(
    ! [A_6] :
      ( k6_domain_1(A_6,'#skF_1'(A_6)) = k1_tarski('#skF_1'(A_6))
      | v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_150])).

tff(c_260,plain,(
    ! [A_81,B_82] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_81),B_82),A_81)
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_264,plain,(
    ! [A_81] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_81))),A_81)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_81)),u1_struct_0(A_81))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | v1_xboole_0(u1_struct_0(A_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_260])).

tff(c_266,plain,(
    ! [A_81] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_81))),A_81)
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | v1_xboole_0(u1_struct_0(A_81)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_264])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_67,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_67])).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_2] : k2_xboole_0(A_2,'#skF_5') = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_8,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),B_5) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_97,plain,(
    ! [A_45,B_46] : k2_xboole_0(k1_tarski(A_45),B_46) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_8])).

tff(c_101,plain,(
    ! [A_45] : k1_tarski(A_45) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_97])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k1_tarski(A_9),k1_zfmisc_1(B_10))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_12])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_6])).

tff(c_542,plain,(
    ! [C_121,B_122,A_123] :
      ( C_121 = B_122
      | ~ r1_tarski(B_122,C_121)
      | ~ v2_tex_2(C_121,A_123)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ v3_tex_2(B_122,A_123)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_544,plain,(
    ! [A_3,A_123] :
      ( A_3 = '#skF_5'
      | ~ v2_tex_2(A_3,A_123)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ v3_tex_2('#skF_5',A_123)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_75,c_542])).

tff(c_592,plain,(
    ! [A_126,A_127] :
      ( A_126 = '#skF_5'
      | ~ v2_tex_2(A_126,A_127)
      | ~ m1_subset_1(A_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ v3_tex_2('#skF_5',A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_544])).

tff(c_610,plain,(
    ! [A_9,A_127] :
      ( k1_tarski(A_9) = '#skF_5'
      | ~ v2_tex_2(k1_tarski(A_9),A_127)
      | ~ v3_tex_2('#skF_5',A_127)
      | ~ l1_pre_topc(A_127)
      | ~ r2_hidden(A_9,u1_struct_0(A_127)) ) ),
    inference(resolution,[status(thm)],[c_14,c_592])).

tff(c_629,plain,(
    ! [A_128,A_129] :
      ( ~ v2_tex_2(k1_tarski(A_128),A_129)
      | ~ v3_tex_2('#skF_5',A_129)
      | ~ l1_pre_topc(A_129)
      | ~ r2_hidden(A_128,u1_struct_0(A_129)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_610])).

tff(c_1079,plain,(
    ! [A_161] :
      ( ~ v3_tex_2('#skF_5',A_161)
      | ~ r2_hidden('#skF_1'(u1_struct_0(A_161)),u1_struct_0(A_161))
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161)
      | v1_xboole_0(u1_struct_0(A_161)) ) ),
    inference(resolution,[status(thm)],[c_266,c_629])).

tff(c_1082,plain,(
    ! [A_161] :
      ( ~ v3_tex_2('#skF_5',A_161)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161)
      | v1_xboole_0(u1_struct_0(A_161))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_161)),u1_struct_0(A_161)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1079])).

tff(c_1086,plain,(
    ! [A_162] :
      ( ~ v3_tex_2('#skF_5',A_162)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162)
      | v1_xboole_0(u1_struct_0(A_162)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1082])).

tff(c_220,plain,(
    ! [A_76] :
      ( m1_subset_1('#skF_2'(A_76),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [B_13,A_11] :
      ( v1_xboole_0(B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_11))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_231,plain,(
    ! [A_76] :
      ( v1_xboole_0('#skF_2'(A_76))
      | ~ v1_xboole_0(u1_struct_0(A_76))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_220,c_16])).

tff(c_1144,plain,(
    ! [A_165] :
      ( v1_xboole_0('#skF_2'(A_165))
      | ~ v3_tex_2('#skF_5',A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_1086,c_231])).

tff(c_24,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0('#skF_2'(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1153,plain,(
    ! [A_166] :
      ( ~ v3_tex_2('#skF_5',A_166)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_1144,c_24])).

tff(c_1159,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1153])).

tff(c_1163,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1159])).

tff(c_1165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.64  
% 3.69/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.64  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 3.69/1.64  
% 3.69/1.64  %Foreground sorts:
% 3.69/1.64  
% 3.69/1.64  
% 3.69/1.64  %Background operators:
% 3.69/1.64  
% 3.69/1.64  
% 3.69/1.64  %Foreground operators:
% 3.69/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.69/1.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.69/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.69/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.69/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.69/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.69/1.64  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.69/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.69/1.64  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.69/1.64  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.69/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.69/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.69/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.69/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.69/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.69/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.64  
% 3.69/1.66  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 3.69/1.66  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.69/1.66  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.69/1.66  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.69/1.66  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 3.69/1.66  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.69/1.66  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.69/1.66  tff(f_36, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.69/1.66  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.69/1.66  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.69/1.66  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.69/1.66  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.69/1.66  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 3.69/1.66  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.69/1.66  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.69/1.66  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.69/1.66  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.69/1.66  tff(c_44, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.69/1.66  tff(c_10, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.69/1.66  tff(c_18, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.69/1.66  tff(c_150, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.66  tff(c_162, plain, (![A_6]: (k6_domain_1(A_6, '#skF_1'(A_6))=k1_tarski('#skF_1'(A_6)) | v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_10, c_150])).
% 3.69/1.66  tff(c_260, plain, (![A_81, B_82]: (v2_tex_2(k6_domain_1(u1_struct_0(A_81), B_82), A_81) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.69/1.66  tff(c_264, plain, (![A_81]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_81))), A_81) | ~m1_subset_1('#skF_1'(u1_struct_0(A_81)), u1_struct_0(A_81)) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | v1_xboole_0(u1_struct_0(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_260])).
% 3.69/1.66  tff(c_266, plain, (![A_81]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_81))), A_81) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | v1_xboole_0(u1_struct_0(A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_264])).
% 3.69/1.66  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.69/1.66  tff(c_67, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.69/1.66  tff(c_71, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_67])).
% 3.69/1.66  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.69/1.66  tff(c_74, plain, (![A_2]: (k2_xboole_0(A_2, '#skF_5')=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_4])).
% 3.69/1.66  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.69/1.66  tff(c_97, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), B_46)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_8])).
% 3.69/1.66  tff(c_101, plain, (![A_45]: (k1_tarski(A_45)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_74, c_97])).
% 3.69/1.66  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(k1_tarski(A_9), k1_zfmisc_1(B_10)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.69/1.66  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.69/1.66  tff(c_73, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_12])).
% 3.69/1.66  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.69/1.66  tff(c_75, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_6])).
% 3.69/1.66  tff(c_542, plain, (![C_121, B_122, A_123]: (C_121=B_122 | ~r1_tarski(B_122, C_121) | ~v2_tex_2(C_121, A_123) | ~m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0(A_123))) | ~v3_tex_2(B_122, A_123) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.69/1.66  tff(c_544, plain, (![A_3, A_123]: (A_3='#skF_5' | ~v2_tex_2(A_3, A_123) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_123))) | ~v3_tex_2('#skF_5', A_123) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_75, c_542])).
% 3.69/1.66  tff(c_592, plain, (![A_126, A_127]: (A_126='#skF_5' | ~v2_tex_2(A_126, A_127) | ~m1_subset_1(A_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~v3_tex_2('#skF_5', A_127) | ~l1_pre_topc(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_544])).
% 3.69/1.66  tff(c_610, plain, (![A_9, A_127]: (k1_tarski(A_9)='#skF_5' | ~v2_tex_2(k1_tarski(A_9), A_127) | ~v3_tex_2('#skF_5', A_127) | ~l1_pre_topc(A_127) | ~r2_hidden(A_9, u1_struct_0(A_127)))), inference(resolution, [status(thm)], [c_14, c_592])).
% 3.69/1.66  tff(c_629, plain, (![A_128, A_129]: (~v2_tex_2(k1_tarski(A_128), A_129) | ~v3_tex_2('#skF_5', A_129) | ~l1_pre_topc(A_129) | ~r2_hidden(A_128, u1_struct_0(A_129)))), inference(negUnitSimplification, [status(thm)], [c_101, c_610])).
% 3.69/1.66  tff(c_1079, plain, (![A_161]: (~v3_tex_2('#skF_5', A_161) | ~r2_hidden('#skF_1'(u1_struct_0(A_161)), u1_struct_0(A_161)) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161) | v1_xboole_0(u1_struct_0(A_161)))), inference(resolution, [status(thm)], [c_266, c_629])).
% 3.69/1.66  tff(c_1082, plain, (![A_161]: (~v3_tex_2('#skF_5', A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161) | v1_xboole_0(u1_struct_0(A_161)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_161)), u1_struct_0(A_161)))), inference(resolution, [status(thm)], [c_18, c_1079])).
% 3.69/1.66  tff(c_1086, plain, (![A_162]: (~v3_tex_2('#skF_5', A_162) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162) | v1_xboole_0(u1_struct_0(A_162)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1082])).
% 3.69/1.66  tff(c_220, plain, (![A_76]: (m1_subset_1('#skF_2'(A_76), k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.69/1.66  tff(c_16, plain, (![B_13, A_11]: (v1_xboole_0(B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_11)) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.69/1.66  tff(c_231, plain, (![A_76]: (v1_xboole_0('#skF_2'(A_76)) | ~v1_xboole_0(u1_struct_0(A_76)) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(resolution, [status(thm)], [c_220, c_16])).
% 3.69/1.66  tff(c_1144, plain, (![A_165]: (v1_xboole_0('#skF_2'(A_165)) | ~v3_tex_2('#skF_5', A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_1086, c_231])).
% 3.69/1.66  tff(c_24, plain, (![A_19]: (~v1_xboole_0('#skF_2'(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.69/1.66  tff(c_1153, plain, (![A_166]: (~v3_tex_2('#skF_5', A_166) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_1144, c_24])).
% 3.69/1.66  tff(c_1159, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1153])).
% 3.69/1.66  tff(c_1163, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1159])).
% 3.69/1.66  tff(c_1165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1163])).
% 3.69/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.66  
% 3.69/1.66  Inference rules
% 3.69/1.66  ----------------------
% 3.69/1.66  #Ref     : 0
% 3.69/1.66  #Sup     : 253
% 3.69/1.66  #Fact    : 0
% 3.69/1.66  #Define  : 0
% 3.69/1.66  #Split   : 3
% 3.69/1.66  #Chain   : 0
% 3.69/1.66  #Close   : 0
% 3.69/1.66  
% 3.69/1.66  Ordering : KBO
% 3.69/1.66  
% 3.69/1.66  Simplification rules
% 3.69/1.66  ----------------------
% 3.69/1.66  #Subsume      : 28
% 3.69/1.66  #Demod        : 32
% 3.69/1.66  #Tautology    : 61
% 3.69/1.66  #SimpNegUnit  : 11
% 3.69/1.66  #BackRed      : 5
% 3.69/1.66  
% 3.69/1.66  #Partial instantiations: 0
% 3.69/1.66  #Strategies tried      : 1
% 3.69/1.66  
% 3.69/1.66  Timing (in seconds)
% 3.69/1.66  ----------------------
% 3.69/1.66  Preprocessing        : 0.34
% 3.69/1.66  Parsing              : 0.19
% 3.69/1.66  CNF conversion       : 0.02
% 3.69/1.66  Main loop            : 0.49
% 3.69/1.66  Inferencing          : 0.19
% 3.69/1.66  Reduction            : 0.13
% 3.69/1.66  Demodulation         : 0.09
% 3.69/1.66  BG Simplification    : 0.02
% 3.69/1.66  Subsumption          : 0.11
% 3.69/1.66  Abstraction          : 0.02
% 3.69/1.66  MUC search           : 0.00
% 3.69/1.66  Cooper               : 0.00
% 3.69/1.66  Total                : 0.86
% 3.69/1.66  Index Insertion      : 0.00
% 3.69/1.66  Index Deletion       : 0.00
% 3.69/1.66  Index Matching       : 0.00
% 3.69/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
