%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:01 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   76 (  97 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  163 ( 226 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_44,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_106,axiom,(
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

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    v3_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1('#skF_2'(A_8),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(A_56,B_57) = k1_tarski(B_57)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_150,plain,(
    ! [A_8] :
      ( k6_domain_1(A_8,'#skF_2'(A_8)) = k1_tarski('#skF_2'(A_8))
      | v1_xboole_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_142])).

tff(c_364,plain,(
    ! [A_81,B_82] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_81),B_82),A_81)
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_368,plain,(
    ! [A_81] :
      ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_81))),A_81)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_81)),u1_struct_0(A_81))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | v1_xboole_0(u1_struct_0(A_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_364])).

tff(c_370,plain,(
    ! [A_81] :
      ( v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_81))),A_81)
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | v1_xboole_0(u1_struct_0(A_81)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_368])).

tff(c_211,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k6_domain_1(A_68,B_69),k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_224,plain,(
    ! [A_8] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_8)),k1_zfmisc_1(A_8))
      | ~ m1_subset_1('#skF_2'(A_8),A_8)
      | v1_xboole_0(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_211])).

tff(c_231,plain,(
    ! [A_8] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_8)),k1_zfmisc_1(A_8))
      | v1_xboole_0(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_224])).

tff(c_59,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_59])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    ! [A_10] : m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,(
    ! [A_6] : r1_tarski('#skF_6',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_10])).

tff(c_702,plain,(
    ! [C_112,B_113,A_114] :
      ( C_112 = B_113
      | ~ r1_tarski(B_113,C_112)
      | ~ v2_tex_2(C_112,A_114)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v3_tex_2(B_113,A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_704,plain,(
    ! [A_6,A_114] :
      ( A_6 = '#skF_6'
      | ~ v2_tex_2(A_6,A_114)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v3_tex_2('#skF_6',A_114)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_70,c_702])).

tff(c_873,plain,(
    ! [A_133,A_134] :
      ( A_133 = '#skF_6'
      | ~ v2_tex_2(A_133,A_134)
      | ~ m1_subset_1(A_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ v3_tex_2('#skF_6',A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_704])).

tff(c_1533,plain,(
    ! [A_169] :
      ( k1_tarski('#skF_2'(u1_struct_0(A_169))) = '#skF_6'
      | ~ v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_169))),A_169)
      | ~ v3_tex_2('#skF_6',A_169)
      | ~ l1_pre_topc(A_169)
      | v1_xboole_0(u1_struct_0(A_169)) ) ),
    inference(resolution,[status(thm)],[c_231,c_873])).

tff(c_1538,plain,(
    ! [A_170] :
      ( k1_tarski('#skF_2'(u1_struct_0(A_170))) = '#skF_6'
      | ~ v3_tex_2('#skF_6',A_170)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170)
      | v1_xboole_0(u1_struct_0(A_170)) ) ),
    inference(resolution,[status(thm)],[c_370,c_1533])).

tff(c_12,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1578,plain,(
    ! [A_170] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ v3_tex_2('#skF_6',A_170)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170)
      | v1_xboole_0(u1_struct_0(A_170)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1538,c_12])).

tff(c_1587,plain,(
    ! [A_171] :
      ( ~ v3_tex_2('#skF_6',A_171)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171)
      | v1_xboole_0(u1_struct_0(A_171)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1578])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_257,plain,(
    ! [A_73] :
      ( m1_subset_1('#skF_3'(A_73),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [C_16,B_15,A_14] :
      ( ~ v1_xboole_0(C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_529,plain,(
    ! [A_94,A_95] :
      ( ~ v1_xboole_0(u1_struct_0(A_94))
      | ~ r2_hidden(A_95,'#skF_3'(A_94))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_257,c_20])).

tff(c_534,plain,(
    ! [A_94] :
      ( ~ v1_xboole_0(u1_struct_0(A_94))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94)
      | v1_xboole_0('#skF_3'(A_94)) ) ),
    inference(resolution,[status(thm)],[c_4,c_529])).

tff(c_1601,plain,(
    ! [A_175] :
      ( v1_xboole_0('#skF_3'(A_175))
      | ~ v3_tex_2('#skF_6',A_175)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_1587,c_534])).

tff(c_24,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0('#skF_3'(A_17))
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1610,plain,(
    ! [A_176] :
      ( ~ v3_tex_2('#skF_6',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_1601,c_24])).

tff(c_1616,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1610])).

tff(c_1620,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1616])).

tff(c_1622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:32:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.38/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.77  
% 4.38/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.78  %$ v4_pre_topc > v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.38/1.78  
% 4.38/1.78  %Foreground sorts:
% 4.38/1.78  
% 4.38/1.78  
% 4.38/1.78  %Background operators:
% 4.38/1.78  
% 4.38/1.78  
% 4.38/1.78  %Foreground operators:
% 4.38/1.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.38/1.78  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.38/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.38/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.38/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.38/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.38/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.38/1.78  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.38/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.38/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.38/1.78  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.38/1.78  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.38/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.38/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.38/1.78  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.38/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.78  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.38/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.38/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.38/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.38/1.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.38/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.38/1.78  
% 4.51/1.79  tff(f_134, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 4.51/1.79  tff(f_44, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.51/1.79  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.51/1.79  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 4.51/1.79  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.51/1.79  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.51/1.79  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.51/1.79  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.51/1.79  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.51/1.79  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.51/1.79  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.51/1.79  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 4.51/1.79  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.51/1.79  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.51/1.79  tff(c_54, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.51/1.79  tff(c_52, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.51/1.79  tff(c_46, plain, (v3_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.51/1.79  tff(c_50, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.51/1.79  tff(c_14, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8), A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.51/1.79  tff(c_142, plain, (![A_56, B_57]: (k6_domain_1(A_56, B_57)=k1_tarski(B_57) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.51/1.79  tff(c_150, plain, (![A_8]: (k6_domain_1(A_8, '#skF_2'(A_8))=k1_tarski('#skF_2'(A_8)) | v1_xboole_0(A_8))), inference(resolution, [status(thm)], [c_14, c_142])).
% 4.51/1.79  tff(c_364, plain, (![A_81, B_82]: (v2_tex_2(k6_domain_1(u1_struct_0(A_81), B_82), A_81) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.51/1.79  tff(c_368, plain, (![A_81]: (v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_81))), A_81) | ~m1_subset_1('#skF_2'(u1_struct_0(A_81)), u1_struct_0(A_81)) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | v1_xboole_0(u1_struct_0(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_364])).
% 4.51/1.79  tff(c_370, plain, (![A_81]: (v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_81))), A_81) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | v1_xboole_0(u1_struct_0(A_81)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_368])).
% 4.51/1.79  tff(c_211, plain, (![A_68, B_69]: (m1_subset_1(k6_domain_1(A_68, B_69), k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.51/1.79  tff(c_224, plain, (![A_8]: (m1_subset_1(k1_tarski('#skF_2'(A_8)), k1_zfmisc_1(A_8)) | ~m1_subset_1('#skF_2'(A_8), A_8) | v1_xboole_0(A_8) | v1_xboole_0(A_8))), inference(superposition, [status(thm), theory('equality')], [c_150, c_211])).
% 4.51/1.79  tff(c_231, plain, (![A_8]: (m1_subset_1(k1_tarski('#skF_2'(A_8)), k1_zfmisc_1(A_8)) | v1_xboole_0(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_224])).
% 4.51/1.79  tff(c_59, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.51/1.79  tff(c_68, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_50, c_59])).
% 4.51/1.79  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.79  tff(c_79, plain, (![A_10]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16])).
% 4.51/1.79  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.51/1.79  tff(c_70, plain, (![A_6]: (r1_tarski('#skF_6', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_10])).
% 4.51/1.79  tff(c_702, plain, (![C_112, B_113, A_114]: (C_112=B_113 | ~r1_tarski(B_113, C_112) | ~v2_tex_2(C_112, A_114) | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_114))) | ~v3_tex_2(B_113, A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.79  tff(c_704, plain, (![A_6, A_114]: (A_6='#skF_6' | ~v2_tex_2(A_6, A_114) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_114))) | ~v3_tex_2('#skF_6', A_114) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_70, c_702])).
% 4.51/1.79  tff(c_873, plain, (![A_133, A_134]: (A_133='#skF_6' | ~v2_tex_2(A_133, A_134) | ~m1_subset_1(A_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~v3_tex_2('#skF_6', A_134) | ~l1_pre_topc(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_704])).
% 4.51/1.79  tff(c_1533, plain, (![A_169]: (k1_tarski('#skF_2'(u1_struct_0(A_169)))='#skF_6' | ~v2_tex_2(k1_tarski('#skF_2'(u1_struct_0(A_169))), A_169) | ~v3_tex_2('#skF_6', A_169) | ~l1_pre_topc(A_169) | v1_xboole_0(u1_struct_0(A_169)))), inference(resolution, [status(thm)], [c_231, c_873])).
% 4.51/1.79  tff(c_1538, plain, (![A_170]: (k1_tarski('#skF_2'(u1_struct_0(A_170)))='#skF_6' | ~v3_tex_2('#skF_6', A_170) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170) | v1_xboole_0(u1_struct_0(A_170)))), inference(resolution, [status(thm)], [c_370, c_1533])).
% 4.51/1.79  tff(c_12, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.51/1.79  tff(c_1578, plain, (![A_170]: (~v1_xboole_0('#skF_6') | ~v3_tex_2('#skF_6', A_170) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170) | v1_xboole_0(u1_struct_0(A_170)))), inference(superposition, [status(thm), theory('equality')], [c_1538, c_12])).
% 4.51/1.79  tff(c_1587, plain, (![A_171]: (~v3_tex_2('#skF_6', A_171) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171) | v1_xboole_0(u1_struct_0(A_171)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1578])).
% 4.51/1.79  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.79  tff(c_257, plain, (![A_73]: (m1_subset_1('#skF_3'(A_73), k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.51/1.79  tff(c_20, plain, (![C_16, B_15, A_14]: (~v1_xboole_0(C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.51/1.79  tff(c_529, plain, (![A_94, A_95]: (~v1_xboole_0(u1_struct_0(A_94)) | ~r2_hidden(A_95, '#skF_3'(A_94)) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_257, c_20])).
% 4.51/1.79  tff(c_534, plain, (![A_94]: (~v1_xboole_0(u1_struct_0(A_94)) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94) | v1_xboole_0('#skF_3'(A_94)))), inference(resolution, [status(thm)], [c_4, c_529])).
% 4.51/1.79  tff(c_1601, plain, (![A_175]: (v1_xboole_0('#skF_3'(A_175)) | ~v3_tex_2('#skF_6', A_175) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(resolution, [status(thm)], [c_1587, c_534])).
% 4.51/1.79  tff(c_24, plain, (![A_17]: (~v1_xboole_0('#skF_3'(A_17)) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.51/1.79  tff(c_1610, plain, (![A_176]: (~v3_tex_2('#skF_6', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_1601, c_24])).
% 4.51/1.79  tff(c_1616, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1610])).
% 4.51/1.79  tff(c_1620, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1616])).
% 4.51/1.79  tff(c_1622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1620])).
% 4.51/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.79  
% 4.51/1.79  Inference rules
% 4.51/1.79  ----------------------
% 4.51/1.79  #Ref     : 0
% 4.51/1.79  #Sup     : 374
% 4.51/1.79  #Fact    : 0
% 4.51/1.79  #Define  : 0
% 4.51/1.79  #Split   : 2
% 4.51/1.79  #Chain   : 0
% 4.51/1.79  #Close   : 0
% 4.51/1.79  
% 4.51/1.79  Ordering : KBO
% 4.51/1.79  
% 4.51/1.79  Simplification rules
% 4.51/1.79  ----------------------
% 4.51/1.79  #Subsume      : 74
% 4.51/1.79  #Demod        : 86
% 4.51/1.79  #Tautology    : 87
% 4.51/1.79  #SimpNegUnit  : 8
% 4.51/1.79  #BackRed      : 6
% 4.51/1.79  
% 4.51/1.79  #Partial instantiations: 0
% 4.51/1.79  #Strategies tried      : 1
% 4.51/1.79  
% 4.51/1.79  Timing (in seconds)
% 4.51/1.79  ----------------------
% 4.51/1.79  Preprocessing        : 0.34
% 4.51/1.80  Parsing              : 0.18
% 4.51/1.80  CNF conversion       : 0.03
% 4.51/1.80  Main loop            : 0.68
% 4.51/1.80  Inferencing          : 0.26
% 4.51/1.80  Reduction            : 0.20
% 4.51/1.80  Demodulation         : 0.13
% 4.51/1.80  BG Simplification    : 0.03
% 4.51/1.80  Subsumption          : 0.14
% 4.51/1.80  Abstraction          : 0.04
% 4.51/1.80  MUC search           : 0.00
% 4.51/1.80  Cooper               : 0.00
% 4.51/1.80  Total                : 1.06
% 4.51/1.80  Index Insertion      : 0.00
% 4.51/1.80  Index Deletion       : 0.00
% 4.51/1.80  Index Matching       : 0.00
% 4.51/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
