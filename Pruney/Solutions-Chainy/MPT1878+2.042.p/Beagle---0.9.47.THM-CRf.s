%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:03 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 136 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  163 ( 309 expanded)
%              Number of equality atoms :   38 (  65 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_32,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_109,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_26,plain,(
    ! [A_28] :
      ( l1_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_68,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_20,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_116,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_1'(A_60),A_60)
      | A_60 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_20])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_120,plain,(
    ! [A_60] :
      ( m1_subset_1('#skF_1'(A_60),A_60)
      | A_60 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_116,c_16])).

tff(c_137,plain,(
    ! [A_68,B_69] :
      ( k6_domain_1(A_68,B_69) = k1_tarski(B_69)
      | ~ m1_subset_1(B_69,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_144,plain,(
    ! [A_60] :
      ( k6_domain_1(A_60,'#skF_1'(A_60)) = k1_tarski('#skF_1'(A_60))
      | v1_xboole_0(A_60)
      | A_60 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_120,c_137])).

tff(c_226,plain,(
    ! [A_97,B_98] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_97),B_98),A_97)
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_559,plain,(
    ! [A_156] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_156))),A_156)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_156)),u1_struct_0(A_156))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | v1_xboole_0(u1_struct_0(A_156))
      | u1_struct_0(A_156) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_226])).

tff(c_6,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_56] : k2_xboole_0(A_56,'#skF_4') = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_6])).

tff(c_10,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),B_5) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),B_5) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_107,plain,(
    ! [A_4] : k1_tarski(A_4) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_92])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(k1_tarski(B_8),k1_zfmisc_1(A_7))
      | k1_xboole_0 = A_7
      | ~ m1_subset_1(B_8,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_160,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(k1_tarski(B_8),k1_zfmisc_1(A_7))
      | A_7 = '#skF_4'
      | ~ m1_subset_1(B_8,A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_14])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_12])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_81,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_8])).

tff(c_432,plain,(
    ! [C_126,B_127,A_128] :
      ( C_126 = B_127
      | ~ r1_tarski(B_127,C_126)
      | ~ v2_tex_2(C_126,A_128)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ v3_tex_2(B_127,A_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_434,plain,(
    ! [A_3,A_128] :
      ( A_3 = '#skF_4'
      | ~ v2_tex_2(A_3,A_128)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ v3_tex_2('#skF_4',A_128)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_81,c_432])).

tff(c_438,plain,(
    ! [A_129,A_130] :
      ( A_129 = '#skF_4'
      | ~ v2_tex_2(A_129,A_130)
      | ~ m1_subset_1(A_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ v3_tex_2('#skF_4',A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_434])).

tff(c_457,plain,(
    ! [B_8,A_130] :
      ( k1_tarski(B_8) = '#skF_4'
      | ~ v2_tex_2(k1_tarski(B_8),A_130)
      | ~ v3_tex_2('#skF_4',A_130)
      | ~ l1_pre_topc(A_130)
      | u1_struct_0(A_130) = '#skF_4'
      | ~ m1_subset_1(B_8,u1_struct_0(A_130)) ) ),
    inference(resolution,[status(thm)],[c_160,c_438])).

tff(c_472,plain,(
    ! [B_8,A_130] :
      ( ~ v2_tex_2(k1_tarski(B_8),A_130)
      | ~ v3_tex_2('#skF_4',A_130)
      | ~ l1_pre_topc(A_130)
      | u1_struct_0(A_130) = '#skF_4'
      | ~ m1_subset_1(B_8,u1_struct_0(A_130)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_457])).

tff(c_564,plain,(
    ! [A_157] :
      ( ~ v3_tex_2('#skF_4',A_157)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_157)),u1_struct_0(A_157))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157)
      | v1_xboole_0(u1_struct_0(A_157))
      | u1_struct_0(A_157) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_559,c_472])).

tff(c_569,plain,(
    ! [A_158] :
      ( ~ v3_tex_2('#skF_4',A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158)
      | v1_xboole_0(u1_struct_0(A_158))
      | u1_struct_0(A_158) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_120,c_564])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_78,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_4])).

tff(c_578,plain,(
    ! [A_159] :
      ( ~ v3_tex_2('#skF_4',A_159)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159)
      | u1_struct_0(A_159) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_569,c_78])).

tff(c_584,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_578])).

tff(c_588,plain,
    ( v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_584])).

tff(c_589,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_588])).

tff(c_28,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(u1_struct_0(A_29))
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_627,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_28])).

tff(c_657,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_627])).

tff(c_658,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_657])).

tff(c_663,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_658])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:29:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.45  
% 3.04/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.45  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.04/1.45  
% 3.04/1.45  %Foreground sorts:
% 3.04/1.45  
% 3.04/1.45  
% 3.04/1.45  %Background operators:
% 3.04/1.45  
% 3.04/1.45  
% 3.04/1.45  %Foreground operators:
% 3.04/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.04/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.04/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.45  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.04/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.04/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.04/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.45  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.04/1.45  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.04/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.04/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.04/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.04/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.04/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.04/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.04/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.45  
% 3.21/1.46  tff(f_137, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 3.21/1.46  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.21/1.46  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.21/1.46  tff(f_72, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.21/1.46  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.21/1.46  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.21/1.46  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 3.21/1.46  tff(f_32, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.21/1.46  tff(f_37, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.21/1.46  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 3.21/1.46  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.21/1.46  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.21/1.46  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.21/1.46  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.21/1.46  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.21/1.46  tff(c_26, plain, (![A_28]: (l1_struct_0(A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.21/1.46  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.21/1.46  tff(c_50, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.21/1.46  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.21/1.46  tff(c_46, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.21/1.46  tff(c_68, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.21/1.46  tff(c_77, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_68])).
% 3.21/1.46  tff(c_20, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.21/1.46  tff(c_116, plain, (![A_60]: (r2_hidden('#skF_1'(A_60), A_60) | A_60='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_20])).
% 3.21/1.46  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.21/1.46  tff(c_120, plain, (![A_60]: (m1_subset_1('#skF_1'(A_60), A_60) | A_60='#skF_4')), inference(resolution, [status(thm)], [c_116, c_16])).
% 3.21/1.46  tff(c_137, plain, (![A_68, B_69]: (k6_domain_1(A_68, B_69)=k1_tarski(B_69) | ~m1_subset_1(B_69, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.21/1.46  tff(c_144, plain, (![A_60]: (k6_domain_1(A_60, '#skF_1'(A_60))=k1_tarski('#skF_1'(A_60)) | v1_xboole_0(A_60) | A_60='#skF_4')), inference(resolution, [status(thm)], [c_120, c_137])).
% 3.21/1.46  tff(c_226, plain, (![A_97, B_98]: (v2_tex_2(k6_domain_1(u1_struct_0(A_97), B_98), A_97) | ~m1_subset_1(B_98, u1_struct_0(A_97)) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.46  tff(c_559, plain, (![A_156]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_156))), A_156) | ~m1_subset_1('#skF_1'(u1_struct_0(A_156)), u1_struct_0(A_156)) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156) | v1_xboole_0(u1_struct_0(A_156)) | u1_struct_0(A_156)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_144, c_226])).
% 3.21/1.46  tff(c_6, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.21/1.46  tff(c_100, plain, (![A_56]: (k2_xboole_0(A_56, '#skF_4')=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_6])).
% 3.21/1.46  tff(c_10, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.46  tff(c_92, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_10])).
% 3.21/1.46  tff(c_107, plain, (![A_4]: (k1_tarski(A_4)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_100, c_92])).
% 3.21/1.46  tff(c_14, plain, (![B_8, A_7]: (m1_subset_1(k1_tarski(B_8), k1_zfmisc_1(A_7)) | k1_xboole_0=A_7 | ~m1_subset_1(B_8, A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.21/1.46  tff(c_160, plain, (![B_8, A_7]: (m1_subset_1(k1_tarski(B_8), k1_zfmisc_1(A_7)) | A_7='#skF_4' | ~m1_subset_1(B_8, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_14])).
% 3.21/1.46  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.46  tff(c_79, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_12])).
% 3.21/1.46  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.21/1.46  tff(c_81, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_8])).
% 3.21/1.46  tff(c_432, plain, (![C_126, B_127, A_128]: (C_126=B_127 | ~r1_tarski(B_127, C_126) | ~v2_tex_2(C_126, A_128) | ~m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0(A_128))) | ~v3_tex_2(B_127, A_128) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.21/1.46  tff(c_434, plain, (![A_3, A_128]: (A_3='#skF_4' | ~v2_tex_2(A_3, A_128) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_128))) | ~v3_tex_2('#skF_4', A_128) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_81, c_432])).
% 3.21/1.46  tff(c_438, plain, (![A_129, A_130]: (A_129='#skF_4' | ~v2_tex_2(A_129, A_130) | ~m1_subset_1(A_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~v3_tex_2('#skF_4', A_130) | ~l1_pre_topc(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_434])).
% 3.21/1.46  tff(c_457, plain, (![B_8, A_130]: (k1_tarski(B_8)='#skF_4' | ~v2_tex_2(k1_tarski(B_8), A_130) | ~v3_tex_2('#skF_4', A_130) | ~l1_pre_topc(A_130) | u1_struct_0(A_130)='#skF_4' | ~m1_subset_1(B_8, u1_struct_0(A_130)))), inference(resolution, [status(thm)], [c_160, c_438])).
% 3.21/1.46  tff(c_472, plain, (![B_8, A_130]: (~v2_tex_2(k1_tarski(B_8), A_130) | ~v3_tex_2('#skF_4', A_130) | ~l1_pre_topc(A_130) | u1_struct_0(A_130)='#skF_4' | ~m1_subset_1(B_8, u1_struct_0(A_130)))), inference(negUnitSimplification, [status(thm)], [c_107, c_457])).
% 3.21/1.46  tff(c_564, plain, (![A_157]: (~v3_tex_2('#skF_4', A_157) | ~m1_subset_1('#skF_1'(u1_struct_0(A_157)), u1_struct_0(A_157)) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157) | v1_xboole_0(u1_struct_0(A_157)) | u1_struct_0(A_157)='#skF_4')), inference(resolution, [status(thm)], [c_559, c_472])).
% 3.21/1.46  tff(c_569, plain, (![A_158]: (~v3_tex_2('#skF_4', A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158) | v1_xboole_0(u1_struct_0(A_158)) | u1_struct_0(A_158)='#skF_4')), inference(resolution, [status(thm)], [c_120, c_564])).
% 3.21/1.46  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.21/1.46  tff(c_78, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_4])).
% 3.21/1.46  tff(c_578, plain, (![A_159]: (~v3_tex_2('#skF_4', A_159) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159) | u1_struct_0(A_159)='#skF_4')), inference(resolution, [status(thm)], [c_569, c_78])).
% 3.21/1.46  tff(c_584, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_578])).
% 3.21/1.46  tff(c_588, plain, (v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_584])).
% 3.21/1.46  tff(c_589, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_588])).
% 3.21/1.46  tff(c_28, plain, (![A_29]: (~v1_xboole_0(u1_struct_0(A_29)) | ~l1_struct_0(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.21/1.46  tff(c_627, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_589, c_28])).
% 3.21/1.46  tff(c_657, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_627])).
% 3.21/1.46  tff(c_658, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_657])).
% 3.21/1.46  tff(c_663, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_658])).
% 3.21/1.46  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_663])).
% 3.21/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.46  
% 3.21/1.46  Inference rules
% 3.21/1.46  ----------------------
% 3.21/1.46  #Ref     : 0
% 3.21/1.46  #Sup     : 122
% 3.21/1.46  #Fact    : 0
% 3.21/1.46  #Define  : 0
% 3.21/1.46  #Split   : 0
% 3.21/1.46  #Chain   : 0
% 3.21/1.46  #Close   : 0
% 3.21/1.46  
% 3.21/1.46  Ordering : KBO
% 3.21/1.46  
% 3.21/1.46  Simplification rules
% 3.21/1.46  ----------------------
% 3.21/1.46  #Subsume      : 3
% 3.21/1.46  #Demod        : 49
% 3.21/1.46  #Tautology    : 32
% 3.21/1.46  #SimpNegUnit  : 8
% 3.21/1.46  #BackRed      : 5
% 3.21/1.46  
% 3.21/1.46  #Partial instantiations: 0
% 3.21/1.46  #Strategies tried      : 1
% 3.21/1.46  
% 3.21/1.46  Timing (in seconds)
% 3.21/1.46  ----------------------
% 3.21/1.47  Preprocessing        : 0.33
% 3.21/1.47  Parsing              : 0.18
% 3.21/1.47  CNF conversion       : 0.02
% 3.21/1.47  Main loop            : 0.36
% 3.21/1.47  Inferencing          : 0.14
% 3.21/1.47  Reduction            : 0.10
% 3.21/1.47  Demodulation         : 0.07
% 3.21/1.47  BG Simplification    : 0.02
% 3.21/1.47  Subsumption          : 0.07
% 3.21/1.47  Abstraction          : 0.02
% 3.21/1.47  MUC search           : 0.00
% 3.21/1.47  Cooper               : 0.00
% 3.21/1.47  Total                : 0.72
% 3.21/1.47  Index Insertion      : 0.00
% 3.21/1.47  Index Deletion       : 0.00
% 3.21/1.47  Index Matching       : 0.00
% 3.21/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
