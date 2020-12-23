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
% DateTime   : Thu Dec  3 10:30:02 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 124 expanded)
%              Number of leaves         :   40 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  143 ( 248 expanded)
%              Number of equality atoms :   25 (  43 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_107,axiom,(
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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_95,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_20,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [A_49,B_50] :
      ( k6_domain_1(A_49,B_50) = k1_tarski(B_50)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_119,plain,(
    ! [A_9] :
      ( k6_domain_1(A_9,'#skF_1'(A_9)) = k1_tarski('#skF_1'(A_9))
      | v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_111])).

tff(c_230,plain,(
    ! [A_72,B_73] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_72),B_73),A_72)
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_234,plain,(
    ! [A_72] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_72))),A_72)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_72)),u1_struct_0(A_72))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72)
      | v1_xboole_0(u1_struct_0(A_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_230])).

tff(c_236,plain,(
    ! [A_72] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_72))),A_72)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72)
      | v1_xboole_0(u1_struct_0(A_72)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_234])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_54,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_54])).

tff(c_8,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_4] : k5_xboole_0(A_4,'#skF_4') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_3] : k4_xboole_0('#skF_4',A_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_6])).

tff(c_98,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k4_xboole_0(B_48,A_47)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_4') = k2_xboole_0(A_3,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_98])).

tff(c_120,plain,(
    ! [A_51] : k2_xboole_0(A_51,'#skF_4') = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_107])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),B_8) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_89,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),B_8) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_127,plain,(
    ! [A_7] : k1_tarski(A_7) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_89])).

tff(c_167,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k6_domain_1(A_63,B_64),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_178,plain,(
    ! [A_9] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_9)),k1_zfmisc_1(A_9))
      | ~ m1_subset_1('#skF_1'(A_9),A_9)
      | v1_xboole_0(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_167])).

tff(c_184,plain,(
    ! [A_9] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_9)),k1_zfmisc_1(A_9))
      | v1_xboole_0(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_178])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_2] : r1_tarski('#skF_4',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4])).

tff(c_451,plain,(
    ! [C_100,B_101,A_102] :
      ( C_100 = B_101
      | ~ r1_tarski(B_101,C_100)
      | ~ v2_tex_2(C_100,A_102)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v3_tex_2(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_453,plain,(
    ! [A_2,A_102] :
      ( A_2 = '#skF_4'
      | ~ v2_tex_2(A_2,A_102)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v3_tex_2('#skF_4',A_102)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_60,c_451])).

tff(c_457,plain,(
    ! [A_103,A_104] :
      ( A_103 = '#skF_4'
      | ~ v2_tex_2(A_103,A_104)
      | ~ m1_subset_1(A_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ v3_tex_2('#skF_4',A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_453])).

tff(c_464,plain,(
    ! [A_104] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_104))) = '#skF_4'
      | ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_104))),A_104)
      | ~ v3_tex_2('#skF_4',A_104)
      | ~ l1_pre_topc(A_104)
      | v1_xboole_0(u1_struct_0(A_104)) ) ),
    inference(resolution,[status(thm)],[c_184,c_457])).

tff(c_485,plain,(
    ! [A_105] :
      ( ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_105))),A_105)
      | ~ v3_tex_2('#skF_4',A_105)
      | ~ l1_pre_topc(A_105)
      | v1_xboole_0(u1_struct_0(A_105)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_464])).

tff(c_490,plain,(
    ! [A_106] :
      ( ~ v3_tex_2('#skF_4',A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106)
      | v1_xboole_0(u1_struct_0(A_106)) ) ),
    inference(resolution,[status(thm)],[c_236,c_485])).

tff(c_22,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_499,plain,(
    ! [A_107] :
      ( ~ l1_struct_0(A_107)
      | ~ v3_tex_2('#skF_4',A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_490,c_22])).

tff(c_505,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_499])).

tff(c_509,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_505])).

tff(c_510,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_509])).

tff(c_513,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_510])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:40:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  
% 2.66/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.66/1.41  
% 2.66/1.41  %Foreground sorts:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Background operators:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Foreground operators:
% 2.66/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.66/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.66/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.66/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.66/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.41  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.66/1.41  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.66/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.66/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.41  
% 2.87/1.43  tff(f_123, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 2.87/1.43  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.87/1.43  tff(f_43, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.87/1.43  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.87/1.43  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.87/1.43  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.87/1.43  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.87/1.43  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.87/1.43  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.87/1.43  tff(f_40, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.87/1.43  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.87/1.43  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.87/1.43  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.87/1.43  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 2.87/1.43  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.87/1.43  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.87/1.43  tff(c_20, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.87/1.43  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.87/1.43  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.87/1.43  tff(c_42, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.87/1.43  tff(c_14, plain, (![A_9]: (m1_subset_1('#skF_1'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.43  tff(c_111, plain, (![A_49, B_50]: (k6_domain_1(A_49, B_50)=k1_tarski(B_50) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.43  tff(c_119, plain, (![A_9]: (k6_domain_1(A_9, '#skF_1'(A_9))=k1_tarski('#skF_1'(A_9)) | v1_xboole_0(A_9))), inference(resolution, [status(thm)], [c_14, c_111])).
% 2.87/1.43  tff(c_230, plain, (![A_72, B_73]: (v2_tex_2(k6_domain_1(u1_struct_0(A_72), B_73), A_72) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.87/1.43  tff(c_234, plain, (![A_72]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_72))), A_72) | ~m1_subset_1('#skF_1'(u1_struct_0(A_72)), u1_struct_0(A_72)) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72) | v1_xboole_0(u1_struct_0(A_72)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_230])).
% 2.87/1.43  tff(c_236, plain, (![A_72]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_72))), A_72) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72) | v1_xboole_0(u1_struct_0(A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_234])).
% 2.87/1.43  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.87/1.43  tff(c_54, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.43  tff(c_58, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_54])).
% 2.87/1.43  tff(c_8, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.43  tff(c_74, plain, (![A_4]: (k5_xboole_0(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8])).
% 2.87/1.43  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.43  tff(c_66, plain, (![A_3]: (k4_xboole_0('#skF_4', A_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_6])).
% 2.87/1.43  tff(c_98, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k4_xboole_0(B_48, A_47))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.43  tff(c_107, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_4')=k2_xboole_0(A_3, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_98])).
% 2.87/1.43  tff(c_120, plain, (![A_51]: (k2_xboole_0(A_51, '#skF_4')=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_107])).
% 2.87/1.43  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.43  tff(c_89, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), B_8)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12])).
% 2.87/1.43  tff(c_127, plain, (![A_7]: (k1_tarski(A_7)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_120, c_89])).
% 2.87/1.43  tff(c_167, plain, (![A_63, B_64]: (m1_subset_1(k6_domain_1(A_63, B_64), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.87/1.43  tff(c_178, plain, (![A_9]: (m1_subset_1(k1_tarski('#skF_1'(A_9)), k1_zfmisc_1(A_9)) | ~m1_subset_1('#skF_1'(A_9), A_9) | v1_xboole_0(A_9) | v1_xboole_0(A_9))), inference(superposition, [status(thm), theory('equality')], [c_119, c_167])).
% 2.87/1.43  tff(c_184, plain, (![A_9]: (m1_subset_1(k1_tarski('#skF_1'(A_9)), k1_zfmisc_1(A_9)) | v1_xboole_0(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_178])).
% 2.87/1.43  tff(c_16, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.87/1.43  tff(c_85, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_16])).
% 2.87/1.43  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.43  tff(c_60, plain, (![A_2]: (r1_tarski('#skF_4', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4])).
% 2.87/1.43  tff(c_451, plain, (![C_100, B_101, A_102]: (C_100=B_101 | ~r1_tarski(B_101, C_100) | ~v2_tex_2(C_100, A_102) | ~m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(A_102))) | ~v3_tex_2(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.87/1.43  tff(c_453, plain, (![A_2, A_102]: (A_2='#skF_4' | ~v2_tex_2(A_2, A_102) | ~m1_subset_1(A_2, k1_zfmisc_1(u1_struct_0(A_102))) | ~v3_tex_2('#skF_4', A_102) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_60, c_451])).
% 2.87/1.43  tff(c_457, plain, (![A_103, A_104]: (A_103='#skF_4' | ~v2_tex_2(A_103, A_104) | ~m1_subset_1(A_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~v3_tex_2('#skF_4', A_104) | ~l1_pre_topc(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_453])).
% 2.87/1.43  tff(c_464, plain, (![A_104]: (k1_tarski('#skF_1'(u1_struct_0(A_104)))='#skF_4' | ~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_104))), A_104) | ~v3_tex_2('#skF_4', A_104) | ~l1_pre_topc(A_104) | v1_xboole_0(u1_struct_0(A_104)))), inference(resolution, [status(thm)], [c_184, c_457])).
% 2.87/1.43  tff(c_485, plain, (![A_105]: (~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_105))), A_105) | ~v3_tex_2('#skF_4', A_105) | ~l1_pre_topc(A_105) | v1_xboole_0(u1_struct_0(A_105)))), inference(negUnitSimplification, [status(thm)], [c_127, c_464])).
% 2.87/1.43  tff(c_490, plain, (![A_106]: (~v3_tex_2('#skF_4', A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106) | v1_xboole_0(u1_struct_0(A_106)))), inference(resolution, [status(thm)], [c_236, c_485])).
% 2.87/1.43  tff(c_22, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.87/1.43  tff(c_499, plain, (![A_107]: (~l1_struct_0(A_107) | ~v3_tex_2('#skF_4', A_107) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(resolution, [status(thm)], [c_490, c_22])).
% 2.87/1.43  tff(c_505, plain, (~l1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_499])).
% 2.87/1.43  tff(c_509, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_505])).
% 2.87/1.43  tff(c_510, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_509])).
% 2.87/1.43  tff(c_513, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_510])).
% 2.87/1.43  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_513])).
% 2.87/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.43  
% 2.87/1.43  Inference rules
% 2.87/1.43  ----------------------
% 2.87/1.43  #Ref     : 0
% 2.87/1.43  #Sup     : 101
% 2.87/1.43  #Fact    : 0
% 2.87/1.43  #Define  : 0
% 2.87/1.43  #Split   : 0
% 2.87/1.43  #Chain   : 0
% 2.87/1.43  #Close   : 0
% 2.87/1.43  
% 2.87/1.43  Ordering : KBO
% 2.87/1.43  
% 2.87/1.43  Simplification rules
% 2.87/1.43  ----------------------
% 2.87/1.43  #Subsume      : 6
% 2.87/1.43  #Demod        : 23
% 2.87/1.43  #Tautology    : 30
% 2.87/1.43  #SimpNegUnit  : 2
% 2.87/1.43  #BackRed      : 2
% 2.87/1.43  
% 2.87/1.43  #Partial instantiations: 0
% 2.87/1.43  #Strategies tried      : 1
% 2.87/1.43  
% 2.87/1.43  Timing (in seconds)
% 2.87/1.43  ----------------------
% 2.87/1.43  Preprocessing        : 0.33
% 2.87/1.43  Parsing              : 0.18
% 2.87/1.43  CNF conversion       : 0.02
% 2.87/1.43  Main loop            : 0.29
% 2.87/1.43  Inferencing          : 0.12
% 2.87/1.43  Reduction            : 0.08
% 2.87/1.43  Demodulation         : 0.06
% 2.87/1.43  BG Simplification    : 0.02
% 2.87/1.43  Subsumption          : 0.05
% 2.87/1.43  Abstraction          : 0.02
% 2.87/1.43  MUC search           : 0.00
% 2.87/1.43  Cooper               : 0.00
% 2.87/1.43  Total                : 0.65
% 2.87/1.43  Index Insertion      : 0.00
% 2.87/1.43  Index Deletion       : 0.00
% 2.87/1.43  Index Matching       : 0.00
% 2.87/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
