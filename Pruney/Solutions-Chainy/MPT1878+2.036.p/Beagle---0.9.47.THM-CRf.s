%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:02 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   70 (  92 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  139 ( 203 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_90,axiom,(
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

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_16,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [A_39,B_40] :
      ( k6_domain_1(A_39,B_40) = k1_tarski(B_40)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_89,plain,(
    ! [A_4] :
      ( k6_domain_1(A_4,'#skF_1'(A_4)) = k1_tarski('#skF_1'(A_4))
      | v1_xboole_0(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_82])).

tff(c_178,plain,(
    ! [A_57,B_58] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_57),B_58),A_57)
      | ~ m1_subset_1(B_58,u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_182,plain,(
    ! [A_57] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_57))),A_57)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_57)),u1_struct_0(A_57))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57)
      | v1_xboole_0(u1_struct_0(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_178])).

tff(c_184,plain,(
    ! [A_57] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_57))),A_57)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57)
      | v1_xboole_0(u1_struct_0(A_57)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_182])).

tff(c_124,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k6_domain_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_135,plain,(
    ! [A_4] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_4)),k1_zfmisc_1(A_4))
      | ~ m1_subset_1('#skF_1'(A_4),A_4)
      | v1_xboole_0(A_4)
      | v1_xboole_0(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_124])).

tff(c_141,plain,(
    ! [A_4] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_4)),k1_zfmisc_1(A_4))
      | v1_xboole_0(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_135])).

tff(c_51,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_60,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_51])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_71,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_12])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_2] : r1_tarski('#skF_4',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6])).

tff(c_381,plain,(
    ! [C_85,B_86,A_87] :
      ( C_85 = B_86
      | ~ r1_tarski(B_86,C_85)
      | ~ v2_tex_2(C_85,A_87)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ v3_tex_2(B_86,A_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_383,plain,(
    ! [A_2,A_87] :
      ( A_2 = '#skF_4'
      | ~ v2_tex_2(A_2,A_87)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ v3_tex_2('#skF_4',A_87)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_62,c_381])).

tff(c_387,plain,(
    ! [A_88,A_89] :
      ( A_88 = '#skF_4'
      | ~ v2_tex_2(A_88,A_89)
      | ~ m1_subset_1(A_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ v3_tex_2('#skF_4',A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_383])).

tff(c_414,plain,(
    ! [A_91] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_91))) = '#skF_4'
      | ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_91))),A_91)
      | ~ v3_tex_2('#skF_4',A_91)
      | ~ l1_pre_topc(A_91)
      | v1_xboole_0(u1_struct_0(A_91)) ) ),
    inference(resolution,[status(thm)],[c_141,c_387])).

tff(c_419,plain,(
    ! [A_92] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_92))) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92)
      | v1_xboole_0(u1_struct_0(A_92)) ) ),
    inference(resolution,[status(thm)],[c_184,c_414])).

tff(c_8,plain,(
    ! [A_3] : ~ v1_xboole_0(k1_tarski(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_445,plain,(
    ! [A_92] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v3_tex_2('#skF_4',A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92)
      | v1_xboole_0(u1_struct_0(A_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_8])).

tff(c_454,plain,(
    ! [A_93] :
      ( ~ v3_tex_2('#skF_4',A_93)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93)
      | v1_xboole_0(u1_struct_0(A_93)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_445])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_470,plain,(
    ! [A_96] :
      ( ~ l1_struct_0(A_96)
      | ~ v3_tex_2('#skF_4',A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_454,c_18])).

tff(c_476,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_470])).

tff(c_480,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_476])).

tff(c_481,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_480])).

tff(c_484,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_481])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:39:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.52  
% 2.82/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.52  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.82/1.52  
% 2.82/1.52  %Foreground sorts:
% 2.82/1.52  
% 2.82/1.52  
% 2.82/1.52  %Background operators:
% 2.82/1.52  
% 2.82/1.52  
% 2.82/1.52  %Foreground operators:
% 2.82/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.82/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.82/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.82/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.52  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.82/1.52  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.82/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.82/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.52  
% 3.02/1.54  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 3.02/1.54  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.02/1.54  tff(f_38, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.02/1.54  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.02/1.54  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 3.02/1.54  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.02/1.54  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.02/1.54  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.02/1.54  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.02/1.54  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.02/1.54  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.02/1.54  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.02/1.54  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.02/1.54  tff(c_16, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.02/1.54  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.02/1.54  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.02/1.54  tff(c_38, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.02/1.54  tff(c_42, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.02/1.54  tff(c_10, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.02/1.54  tff(c_82, plain, (![A_39, B_40]: (k6_domain_1(A_39, B_40)=k1_tarski(B_40) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.02/1.54  tff(c_89, plain, (![A_4]: (k6_domain_1(A_4, '#skF_1'(A_4))=k1_tarski('#skF_1'(A_4)) | v1_xboole_0(A_4))), inference(resolution, [status(thm)], [c_10, c_82])).
% 3.02/1.54  tff(c_178, plain, (![A_57, B_58]: (v2_tex_2(k6_domain_1(u1_struct_0(A_57), B_58), A_57) | ~m1_subset_1(B_58, u1_struct_0(A_57)) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.02/1.54  tff(c_182, plain, (![A_57]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_57))), A_57) | ~m1_subset_1('#skF_1'(u1_struct_0(A_57)), u1_struct_0(A_57)) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57) | v1_xboole_0(u1_struct_0(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_178])).
% 3.02/1.54  tff(c_184, plain, (![A_57]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_57))), A_57) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57) | v1_xboole_0(u1_struct_0(A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_182])).
% 3.02/1.54  tff(c_124, plain, (![A_51, B_52]: (m1_subset_1(k6_domain_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.02/1.54  tff(c_135, plain, (![A_4]: (m1_subset_1(k1_tarski('#skF_1'(A_4)), k1_zfmisc_1(A_4)) | ~m1_subset_1('#skF_1'(A_4), A_4) | v1_xboole_0(A_4) | v1_xboole_0(A_4))), inference(superposition, [status(thm), theory('equality')], [c_89, c_124])).
% 3.02/1.54  tff(c_141, plain, (![A_4]: (m1_subset_1(k1_tarski('#skF_1'(A_4)), k1_zfmisc_1(A_4)) | v1_xboole_0(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_135])).
% 3.02/1.54  tff(c_51, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.02/1.54  tff(c_60, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_51])).
% 3.02/1.54  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.02/1.54  tff(c_71, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_12])).
% 3.02/1.54  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.02/1.54  tff(c_62, plain, (![A_2]: (r1_tarski('#skF_4', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6])).
% 3.02/1.54  tff(c_381, plain, (![C_85, B_86, A_87]: (C_85=B_86 | ~r1_tarski(B_86, C_85) | ~v2_tex_2(C_85, A_87) | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(A_87))) | ~v3_tex_2(B_86, A_87) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.02/1.54  tff(c_383, plain, (![A_2, A_87]: (A_2='#skF_4' | ~v2_tex_2(A_2, A_87) | ~m1_subset_1(A_2, k1_zfmisc_1(u1_struct_0(A_87))) | ~v3_tex_2('#skF_4', A_87) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_62, c_381])).
% 3.02/1.54  tff(c_387, plain, (![A_88, A_89]: (A_88='#skF_4' | ~v2_tex_2(A_88, A_89) | ~m1_subset_1(A_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~v3_tex_2('#skF_4', A_89) | ~l1_pre_topc(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_383])).
% 3.02/1.54  tff(c_414, plain, (![A_91]: (k1_tarski('#skF_1'(u1_struct_0(A_91)))='#skF_4' | ~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_91))), A_91) | ~v3_tex_2('#skF_4', A_91) | ~l1_pre_topc(A_91) | v1_xboole_0(u1_struct_0(A_91)))), inference(resolution, [status(thm)], [c_141, c_387])).
% 3.02/1.54  tff(c_419, plain, (![A_92]: (k1_tarski('#skF_1'(u1_struct_0(A_92)))='#skF_4' | ~v3_tex_2('#skF_4', A_92) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92) | v1_xboole_0(u1_struct_0(A_92)))), inference(resolution, [status(thm)], [c_184, c_414])).
% 3.02/1.54  tff(c_8, plain, (![A_3]: (~v1_xboole_0(k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.54  tff(c_445, plain, (![A_92]: (~v1_xboole_0('#skF_4') | ~v3_tex_2('#skF_4', A_92) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92) | v1_xboole_0(u1_struct_0(A_92)))), inference(superposition, [status(thm), theory('equality')], [c_419, c_8])).
% 3.02/1.54  tff(c_454, plain, (![A_93]: (~v3_tex_2('#skF_4', A_93) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93) | v1_xboole_0(u1_struct_0(A_93)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_445])).
% 3.02/1.54  tff(c_18, plain, (![A_11]: (~v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.02/1.54  tff(c_470, plain, (![A_96]: (~l1_struct_0(A_96) | ~v3_tex_2('#skF_4', A_96) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_454, c_18])).
% 3.02/1.54  tff(c_476, plain, (~l1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_470])).
% 3.02/1.54  tff(c_480, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_476])).
% 3.02/1.54  tff(c_481, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_480])).
% 3.02/1.54  tff(c_484, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_481])).
% 3.02/1.54  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_484])).
% 3.02/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.54  
% 3.02/1.54  Inference rules
% 3.02/1.54  ----------------------
% 3.02/1.54  #Ref     : 0
% 3.02/1.54  #Sup     : 96
% 3.02/1.54  #Fact    : 0
% 3.02/1.54  #Define  : 0
% 3.02/1.54  #Split   : 0
% 3.02/1.54  #Chain   : 0
% 3.02/1.54  #Close   : 0
% 3.02/1.54  
% 3.02/1.54  Ordering : KBO
% 3.02/1.54  
% 3.02/1.54  Simplification rules
% 3.02/1.54  ----------------------
% 3.02/1.54  #Subsume      : 10
% 3.02/1.54  #Demod        : 22
% 3.02/1.54  #Tautology    : 25
% 3.02/1.54  #SimpNegUnit  : 1
% 3.02/1.54  #BackRed      : 3
% 3.02/1.54  
% 3.02/1.54  #Partial instantiations: 0
% 3.02/1.54  #Strategies tried      : 1
% 3.02/1.54  
% 3.02/1.54  Timing (in seconds)
% 3.02/1.54  ----------------------
% 3.02/1.54  Preprocessing        : 0.38
% 3.02/1.54  Parsing              : 0.19
% 3.02/1.54  CNF conversion       : 0.02
% 3.02/1.54  Main loop            : 0.30
% 3.02/1.54  Inferencing          : 0.12
% 3.04/1.54  Reduction            : 0.09
% 3.04/1.54  Demodulation         : 0.06
% 3.04/1.54  BG Simplification    : 0.02
% 3.04/1.54  Subsumption          : 0.05
% 3.04/1.54  Abstraction          : 0.02
% 3.04/1.54  MUC search           : 0.00
% 3.04/1.54  Cooper               : 0.00
% 3.04/1.54  Total                : 0.71
% 3.04/1.54  Index Insertion      : 0.00
% 3.04/1.54  Index Deletion       : 0.00
% 3.04/1.54  Index Matching       : 0.00
% 3.04/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
