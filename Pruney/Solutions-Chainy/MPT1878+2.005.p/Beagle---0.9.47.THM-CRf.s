%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:58 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   72 (  93 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  154 ( 217 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_100,axiom,(
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

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_125,plain,(
    ! [A_47,B_48] :
      ( k6_domain_1(A_47,B_48) = k1_tarski(B_48)
      | ~ m1_subset_1(B_48,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_133,plain,(
    ! [A_4] :
      ( k6_domain_1(A_4,'#skF_1'(A_4)) = k1_tarski('#skF_1'(A_4))
      | v1_xboole_0(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_299,plain,(
    ! [A_74,B_75] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_74),B_75),A_74)
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_303,plain,(
    ! [A_74] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_74))),A_74)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_74)),u1_struct_0(A_74))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74)
      | v1_xboole_0(u1_struct_0(A_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_299])).

tff(c_305,plain,(
    ! [A_74] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_74))),A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74)
      | v1_xboole_0(u1_struct_0(A_74)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_303])).

tff(c_173,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k6_domain_1(A_59,B_60),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_187,plain,(
    ! [A_4] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_4)),k1_zfmisc_1(A_4))
      | ~ m1_subset_1('#skF_1'(A_4),A_4)
      | v1_xboole_0(A_4)
      | v1_xboole_0(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_173])).

tff(c_194,plain,(
    ! [A_4] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_4)),k1_zfmisc_1(A_4))
      | v1_xboole_0(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_187])).

tff(c_56,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_65,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_56])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_67,plain,(
    ! [A_6] : m1_subset_1('#skF_5',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_12])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    ! [A_2] : r1_tarski('#skF_5',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_6])).

tff(c_564,plain,(
    ! [C_107,B_108,A_109] :
      ( C_107 = B_108
      | ~ r1_tarski(B_108,C_107)
      | ~ v2_tex_2(C_107,A_109)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ v3_tex_2(B_108,A_109)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_566,plain,(
    ! [A_2,A_109] :
      ( A_2 = '#skF_5'
      | ~ v2_tex_2(A_2,A_109)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ v3_tex_2('#skF_5',A_109)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_68,c_564])).

tff(c_570,plain,(
    ! [A_110,A_111] :
      ( A_110 = '#skF_5'
      | ~ v2_tex_2(A_110,A_111)
      | ~ m1_subset_1(A_110,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ v3_tex_2('#skF_5',A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_566])).

tff(c_627,plain,(
    ! [A_115] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_115))) = '#skF_5'
      | ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_115))),A_115)
      | ~ v3_tex_2('#skF_5',A_115)
      | ~ l1_pre_topc(A_115)
      | v1_xboole_0(u1_struct_0(A_115)) ) ),
    inference(resolution,[status(thm)],[c_194,c_570])).

tff(c_632,plain,(
    ! [A_116] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_116))) = '#skF_5'
      | ~ v3_tex_2('#skF_5',A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116)
      | v1_xboole_0(u1_struct_0(A_116)) ) ),
    inference(resolution,[status(thm)],[c_305,c_627])).

tff(c_8,plain,(
    ! [A_3] : ~ v1_xboole_0(k1_tarski(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_658,plain,(
    ! [A_116] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ v3_tex_2('#skF_5',A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116)
      | v1_xboole_0(u1_struct_0(A_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_8])).

tff(c_667,plain,(
    ! [A_117] :
      ( ~ v3_tex_2('#skF_5',A_117)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117)
      | v1_xboole_0(u1_struct_0(A_117)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_658])).

tff(c_195,plain,(
    ! [A_61] :
      ( m1_subset_1('#skF_2'(A_61),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_206,plain,(
    ! [A_61] :
      ( v1_xboole_0('#skF_2'(A_61))
      | ~ v1_xboole_0(u1_struct_0(A_61))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_195,c_14])).

tff(c_676,plain,(
    ! [A_118] :
      ( v1_xboole_0('#skF_2'(A_118))
      | ~ v3_tex_2('#skF_5',A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_667,c_206])).

tff(c_20,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0('#skF_2'(A_13))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_685,plain,(
    ! [A_119] :
      ( ~ v3_tex_2('#skF_5',A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_676,c_20])).

tff(c_691,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_685])).

tff(c_695,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_691])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_695])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:51:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.42  
% 2.95/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.42  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_4
% 2.95/1.42  
% 2.95/1.42  %Foreground sorts:
% 2.95/1.42  
% 2.95/1.42  
% 2.95/1.42  %Background operators:
% 2.95/1.42  
% 2.95/1.42  
% 2.95/1.42  %Foreground operators:
% 2.95/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.95/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.95/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.95/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.95/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.95/1.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.95/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.42  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.95/1.42  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.95/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.95/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.95/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.43  
% 2.95/1.44  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 2.95/1.44  tff(f_38, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.95/1.44  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.95/1.44  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.95/1.44  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.95/1.44  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.95/1.44  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.95/1.44  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.95/1.44  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.95/1.44  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.95/1.44  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 2.95/1.44  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.95/1.44  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.44  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.44  tff(c_48, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.44  tff(c_42, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.44  tff(c_46, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.95/1.44  tff(c_10, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.95/1.44  tff(c_125, plain, (![A_47, B_48]: (k6_domain_1(A_47, B_48)=k1_tarski(B_48) | ~m1_subset_1(B_48, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.95/1.44  tff(c_133, plain, (![A_4]: (k6_domain_1(A_4, '#skF_1'(A_4))=k1_tarski('#skF_1'(A_4)) | v1_xboole_0(A_4))), inference(resolution, [status(thm)], [c_10, c_125])).
% 2.95/1.44  tff(c_299, plain, (![A_74, B_75]: (v2_tex_2(k6_domain_1(u1_struct_0(A_74), B_75), A_74) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.95/1.44  tff(c_303, plain, (![A_74]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_74))), A_74) | ~m1_subset_1('#skF_1'(u1_struct_0(A_74)), u1_struct_0(A_74)) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74) | v1_xboole_0(u1_struct_0(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_299])).
% 2.95/1.44  tff(c_305, plain, (![A_74]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_74))), A_74) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74) | v1_xboole_0(u1_struct_0(A_74)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_303])).
% 2.95/1.44  tff(c_173, plain, (![A_59, B_60]: (m1_subset_1(k6_domain_1(A_59, B_60), k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.95/1.44  tff(c_187, plain, (![A_4]: (m1_subset_1(k1_tarski('#skF_1'(A_4)), k1_zfmisc_1(A_4)) | ~m1_subset_1('#skF_1'(A_4), A_4) | v1_xboole_0(A_4) | v1_xboole_0(A_4))), inference(superposition, [status(thm), theory('equality')], [c_133, c_173])).
% 2.95/1.44  tff(c_194, plain, (![A_4]: (m1_subset_1(k1_tarski('#skF_1'(A_4)), k1_zfmisc_1(A_4)) | v1_xboole_0(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_187])).
% 2.95/1.44  tff(c_56, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.95/1.44  tff(c_65, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_56])).
% 2.95/1.44  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.95/1.44  tff(c_67, plain, (![A_6]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_12])).
% 2.95/1.44  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.95/1.44  tff(c_68, plain, (![A_2]: (r1_tarski('#skF_5', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_6])).
% 2.95/1.44  tff(c_564, plain, (![C_107, B_108, A_109]: (C_107=B_108 | ~r1_tarski(B_108, C_107) | ~v2_tex_2(C_107, A_109) | ~m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_109))) | ~v3_tex_2(B_108, A_109) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.95/1.44  tff(c_566, plain, (![A_2, A_109]: (A_2='#skF_5' | ~v2_tex_2(A_2, A_109) | ~m1_subset_1(A_2, k1_zfmisc_1(u1_struct_0(A_109))) | ~v3_tex_2('#skF_5', A_109) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_68, c_564])).
% 2.95/1.44  tff(c_570, plain, (![A_110, A_111]: (A_110='#skF_5' | ~v2_tex_2(A_110, A_111) | ~m1_subset_1(A_110, k1_zfmisc_1(u1_struct_0(A_111))) | ~v3_tex_2('#skF_5', A_111) | ~l1_pre_topc(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_566])).
% 2.95/1.44  tff(c_627, plain, (![A_115]: (k1_tarski('#skF_1'(u1_struct_0(A_115)))='#skF_5' | ~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_115))), A_115) | ~v3_tex_2('#skF_5', A_115) | ~l1_pre_topc(A_115) | v1_xboole_0(u1_struct_0(A_115)))), inference(resolution, [status(thm)], [c_194, c_570])).
% 2.95/1.44  tff(c_632, plain, (![A_116]: (k1_tarski('#skF_1'(u1_struct_0(A_116)))='#skF_5' | ~v3_tex_2('#skF_5', A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116) | v1_xboole_0(u1_struct_0(A_116)))), inference(resolution, [status(thm)], [c_305, c_627])).
% 2.95/1.44  tff(c_8, plain, (![A_3]: (~v1_xboole_0(k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.44  tff(c_658, plain, (![A_116]: (~v1_xboole_0('#skF_5') | ~v3_tex_2('#skF_5', A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116) | v1_xboole_0(u1_struct_0(A_116)))), inference(superposition, [status(thm), theory('equality')], [c_632, c_8])).
% 2.95/1.44  tff(c_667, plain, (![A_117]: (~v3_tex_2('#skF_5', A_117) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117) | v1_xboole_0(u1_struct_0(A_117)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_658])).
% 2.95/1.44  tff(c_195, plain, (![A_61]: (m1_subset_1('#skF_2'(A_61), k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.95/1.44  tff(c_14, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.95/1.44  tff(c_206, plain, (![A_61]: (v1_xboole_0('#skF_2'(A_61)) | ~v1_xboole_0(u1_struct_0(A_61)) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(resolution, [status(thm)], [c_195, c_14])).
% 2.95/1.44  tff(c_676, plain, (![A_118]: (v1_xboole_0('#skF_2'(A_118)) | ~v3_tex_2('#skF_5', A_118) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(resolution, [status(thm)], [c_667, c_206])).
% 2.95/1.44  tff(c_20, plain, (![A_13]: (~v1_xboole_0('#skF_2'(A_13)) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.95/1.44  tff(c_685, plain, (![A_119]: (~v3_tex_2('#skF_5', A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(resolution, [status(thm)], [c_676, c_20])).
% 2.95/1.44  tff(c_691, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_685])).
% 2.95/1.44  tff(c_695, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_691])).
% 2.95/1.44  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_695])).
% 2.95/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.44  
% 2.95/1.44  Inference rules
% 2.95/1.44  ----------------------
% 2.95/1.44  #Ref     : 0
% 2.95/1.44  #Sup     : 149
% 2.95/1.44  #Fact    : 0
% 2.95/1.44  #Define  : 0
% 2.95/1.44  #Split   : 0
% 2.95/1.44  #Chain   : 0
% 2.95/1.44  #Close   : 0
% 2.95/1.44  
% 2.95/1.44  Ordering : KBO
% 2.95/1.44  
% 2.95/1.44  Simplification rules
% 2.95/1.44  ----------------------
% 2.95/1.44  #Subsume      : 22
% 2.95/1.44  #Demod        : 24
% 2.95/1.44  #Tautology    : 38
% 2.95/1.44  #SimpNegUnit  : 4
% 2.95/1.44  #BackRed      : 4
% 2.95/1.44  
% 2.95/1.44  #Partial instantiations: 0
% 2.95/1.44  #Strategies tried      : 1
% 2.95/1.44  
% 2.95/1.44  Timing (in seconds)
% 2.95/1.44  ----------------------
% 2.95/1.44  Preprocessing        : 0.32
% 2.95/1.44  Parsing              : 0.17
% 2.95/1.44  CNF conversion       : 0.02
% 2.95/1.44  Main loop            : 0.36
% 2.95/1.44  Inferencing          : 0.14
% 2.95/1.44  Reduction            : 0.10
% 2.95/1.44  Demodulation         : 0.06
% 2.95/1.44  BG Simplification    : 0.02
% 2.95/1.44  Subsumption          : 0.07
% 2.95/1.44  Abstraction          : 0.02
% 2.95/1.44  MUC search           : 0.00
% 2.95/1.44  Cooper               : 0.00
% 2.95/1.44  Total                : 0.71
% 2.95/1.44  Index Insertion      : 0.00
% 2.95/1.44  Index Deletion       : 0.00
% 2.95/1.44  Index Matching       : 0.00
% 2.95/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
