%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:03 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 135 expanded)
%              Number of leaves         :   37 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  160 ( 303 expanded)
%              Number of equality atoms :   37 (  63 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
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

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_54,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_63,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_54])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_100,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | A_2 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_6])).

tff(c_102,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),A_2)
      | A_2 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_100,c_102])).

tff(c_128,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(A_56,B_57) = k1_tarski(B_57)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_185,plain,(
    ! [A_67] :
      ( k6_domain_1(A_67,'#skF_1'(A_67)) = k1_tarski('#skF_1'(A_67))
      | v1_xboole_0(A_67)
      | A_67 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_106,c_128])).

tff(c_40,plain,(
    ! [A_30,B_32] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_30),B_32),A_30)
      | ~ m1_subset_1(B_32,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_524,plain,(
    ! [A_126] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_126))),A_126)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_126)),u1_struct_0(A_126))
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126)
      | v1_xboole_0(u1_struct_0(A_126))
      | u1_struct_0(A_126) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_40])).

tff(c_8,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    ! [A_4] : k2_xboole_0(A_4,'#skF_4') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_8])).

tff(c_12,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),B_7) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [A_41,B_42] : k2_xboole_0(k1_tarski(A_41),B_42) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_12])).

tff(c_98,plain,(
    ! [A_41] : k1_tarski(A_41) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_94])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(k1_tarski(B_10),k1_zfmisc_1(A_9))
      | k1_xboole_0 = A_9
      | ~ m1_subset_1(B_10,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_123,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(k1_tarski(B_10),k1_zfmisc_1(A_9))
      | A_9 = '#skF_4'
      | ~ m1_subset_1(B_10,A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_16])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_14])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_10])).

tff(c_406,plain,(
    ! [C_98,B_99,A_100] :
      ( C_98 = B_99
      | ~ r1_tarski(B_99,C_98)
      | ~ v2_tex_2(C_98,A_100)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v3_tex_2(B_99,A_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_408,plain,(
    ! [A_5,A_100] :
      ( A_5 = '#skF_4'
      | ~ v2_tex_2(A_5,A_100)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v3_tex_2('#skF_4',A_100)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_65,c_406])).

tff(c_412,plain,(
    ! [A_101,A_102] :
      ( A_101 = '#skF_4'
      | ~ v2_tex_2(A_101,A_102)
      | ~ m1_subset_1(A_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v3_tex_2('#skF_4',A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_408])).

tff(c_431,plain,(
    ! [B_10,A_102] :
      ( k1_tarski(B_10) = '#skF_4'
      | ~ v2_tex_2(k1_tarski(B_10),A_102)
      | ~ v3_tex_2('#skF_4',A_102)
      | ~ l1_pre_topc(A_102)
      | u1_struct_0(A_102) = '#skF_4'
      | ~ m1_subset_1(B_10,u1_struct_0(A_102)) ) ),
    inference(resolution,[status(thm)],[c_123,c_412])).

tff(c_446,plain,(
    ! [B_10,A_102] :
      ( ~ v2_tex_2(k1_tarski(B_10),A_102)
      | ~ v3_tex_2('#skF_4',A_102)
      | ~ l1_pre_topc(A_102)
      | u1_struct_0(A_102) = '#skF_4'
      | ~ m1_subset_1(B_10,u1_struct_0(A_102)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_431])).

tff(c_529,plain,(
    ! [A_127] :
      ( ~ v3_tex_2('#skF_4',A_127)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_127)),u1_struct_0(A_127))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127)
      | v1_xboole_0(u1_struct_0(A_127))
      | u1_struct_0(A_127) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_524,c_446])).

tff(c_543,plain,(
    ! [A_130] :
      ( ~ v3_tex_2('#skF_4',A_130)
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130)
      | v1_xboole_0(u1_struct_0(A_130))
      | u1_struct_0(A_130) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_106,c_529])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_64,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_4])).

tff(c_552,plain,(
    ! [A_131] :
      ( ~ v3_tex_2('#skF_4',A_131)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131)
      | u1_struct_0(A_131) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_543,c_64])).

tff(c_558,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_552])).

tff(c_562,plain,
    ( v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_558])).

tff(c_563,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_562])).

tff(c_24,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_601,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_24])).

tff(c_631,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_601])).

tff(c_632,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_631])).

tff(c_636,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_632])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.42  
% 2.79/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.42  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.79/1.42  
% 2.79/1.42  %Foreground sorts:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Background operators:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Foreground operators:
% 2.79/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.79/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.79/1.42  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.79/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.42  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.79/1.42  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.79/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.79/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.79/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.79/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.79/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.42  
% 3.09/1.44  tff(f_129, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 3.09/1.44  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.09/1.44  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.09/1.44  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.09/1.44  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.09/1.44  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.09/1.44  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 3.09/1.44  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.09/1.44  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.09/1.44  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 3.09/1.44  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.09/1.44  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.09/1.44  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.09/1.44  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.09/1.44  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.09/1.44  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.09/1.44  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.09/1.44  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.09/1.44  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.09/1.44  tff(c_42, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.09/1.44  tff(c_54, plain, (![A_35]: (k1_xboole_0=A_35 | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.09/1.44  tff(c_63, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_54])).
% 3.09/1.44  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.09/1.44  tff(c_100, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_6])).
% 3.09/1.44  tff(c_102, plain, (![A_45, B_46]: (m1_subset_1(A_45, B_46) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.44  tff(c_106, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2) | A_2='#skF_4')), inference(resolution, [status(thm)], [c_100, c_102])).
% 3.09/1.44  tff(c_128, plain, (![A_56, B_57]: (k6_domain_1(A_56, B_57)=k1_tarski(B_57) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.09/1.44  tff(c_185, plain, (![A_67]: (k6_domain_1(A_67, '#skF_1'(A_67))=k1_tarski('#skF_1'(A_67)) | v1_xboole_0(A_67) | A_67='#skF_4')), inference(resolution, [status(thm)], [c_106, c_128])).
% 3.09/1.44  tff(c_40, plain, (![A_30, B_32]: (v2_tex_2(k6_domain_1(u1_struct_0(A_30), B_32), A_30) | ~m1_subset_1(B_32, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.09/1.44  tff(c_524, plain, (![A_126]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_126))), A_126) | ~m1_subset_1('#skF_1'(u1_struct_0(A_126)), u1_struct_0(A_126)) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126) | v1_xboole_0(u1_struct_0(A_126)) | u1_struct_0(A_126)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_185, c_40])).
% 3.09/1.44  tff(c_8, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.09/1.44  tff(c_76, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_8])).
% 3.09/1.44  tff(c_12, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.09/1.44  tff(c_94, plain, (![A_41, B_42]: (k2_xboole_0(k1_tarski(A_41), B_42)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_12])).
% 3.09/1.44  tff(c_98, plain, (![A_41]: (k1_tarski(A_41)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_76, c_94])).
% 3.09/1.44  tff(c_16, plain, (![B_10, A_9]: (m1_subset_1(k1_tarski(B_10), k1_zfmisc_1(A_9)) | k1_xboole_0=A_9 | ~m1_subset_1(B_10, A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.09/1.44  tff(c_123, plain, (![B_10, A_9]: (m1_subset_1(k1_tarski(B_10), k1_zfmisc_1(A_9)) | A_9='#skF_4' | ~m1_subset_1(B_10, A_9))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_16])).
% 3.09/1.44  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.44  tff(c_73, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_14])).
% 3.09/1.44  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.09/1.44  tff(c_65, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10])).
% 3.09/1.44  tff(c_406, plain, (![C_98, B_99, A_100]: (C_98=B_99 | ~r1_tarski(B_99, C_98) | ~v2_tex_2(C_98, A_100) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_100))) | ~v3_tex_2(B_99, A_100) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.09/1.44  tff(c_408, plain, (![A_5, A_100]: (A_5='#skF_4' | ~v2_tex_2(A_5, A_100) | ~m1_subset_1(A_5, k1_zfmisc_1(u1_struct_0(A_100))) | ~v3_tex_2('#skF_4', A_100) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_65, c_406])).
% 3.09/1.44  tff(c_412, plain, (![A_101, A_102]: (A_101='#skF_4' | ~v2_tex_2(A_101, A_102) | ~m1_subset_1(A_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~v3_tex_2('#skF_4', A_102) | ~l1_pre_topc(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_408])).
% 3.09/1.44  tff(c_431, plain, (![B_10, A_102]: (k1_tarski(B_10)='#skF_4' | ~v2_tex_2(k1_tarski(B_10), A_102) | ~v3_tex_2('#skF_4', A_102) | ~l1_pre_topc(A_102) | u1_struct_0(A_102)='#skF_4' | ~m1_subset_1(B_10, u1_struct_0(A_102)))), inference(resolution, [status(thm)], [c_123, c_412])).
% 3.09/1.44  tff(c_446, plain, (![B_10, A_102]: (~v2_tex_2(k1_tarski(B_10), A_102) | ~v3_tex_2('#skF_4', A_102) | ~l1_pre_topc(A_102) | u1_struct_0(A_102)='#skF_4' | ~m1_subset_1(B_10, u1_struct_0(A_102)))), inference(negUnitSimplification, [status(thm)], [c_98, c_431])).
% 3.09/1.44  tff(c_529, plain, (![A_127]: (~v3_tex_2('#skF_4', A_127) | ~m1_subset_1('#skF_1'(u1_struct_0(A_127)), u1_struct_0(A_127)) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127) | v1_xboole_0(u1_struct_0(A_127)) | u1_struct_0(A_127)='#skF_4')), inference(resolution, [status(thm)], [c_524, c_446])).
% 3.09/1.44  tff(c_543, plain, (![A_130]: (~v3_tex_2('#skF_4', A_130) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130) | v1_xboole_0(u1_struct_0(A_130)) | u1_struct_0(A_130)='#skF_4')), inference(resolution, [status(thm)], [c_106, c_529])).
% 3.09/1.44  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.09/1.44  tff(c_64, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_4])).
% 3.09/1.44  tff(c_552, plain, (![A_131]: (~v3_tex_2('#skF_4', A_131) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131) | u1_struct_0(A_131)='#skF_4')), inference(resolution, [status(thm)], [c_543, c_64])).
% 3.09/1.44  tff(c_558, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_42, c_552])).
% 3.09/1.44  tff(c_562, plain, (v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_558])).
% 3.09/1.44  tff(c_563, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_562])).
% 3.09/1.44  tff(c_24, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.09/1.44  tff(c_601, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_563, c_24])).
% 3.09/1.44  tff(c_631, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_601])).
% 3.09/1.44  tff(c_632, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_631])).
% 3.09/1.44  tff(c_636, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_632])).
% 3.09/1.44  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_636])).
% 3.09/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.44  
% 3.09/1.44  Inference rules
% 3.09/1.44  ----------------------
% 3.09/1.44  #Ref     : 0
% 3.09/1.44  #Sup     : 118
% 3.09/1.44  #Fact    : 0
% 3.09/1.44  #Define  : 0
% 3.09/1.44  #Split   : 0
% 3.09/1.44  #Chain   : 0
% 3.09/1.44  #Close   : 0
% 3.09/1.44  
% 3.09/1.44  Ordering : KBO
% 3.09/1.44  
% 3.09/1.44  Simplification rules
% 3.09/1.44  ----------------------
% 3.09/1.44  #Subsume      : 3
% 3.09/1.44  #Demod        : 47
% 3.09/1.44  #Tautology    : 30
% 3.09/1.44  #SimpNegUnit  : 8
% 3.09/1.44  #BackRed      : 3
% 3.09/1.44  
% 3.09/1.44  #Partial instantiations: 0
% 3.09/1.44  #Strategies tried      : 1
% 3.09/1.44  
% 3.09/1.44  Timing (in seconds)
% 3.09/1.44  ----------------------
% 3.09/1.44  Preprocessing        : 0.31
% 3.09/1.44  Parsing              : 0.17
% 3.09/1.44  CNF conversion       : 0.02
% 3.09/1.44  Main loop            : 0.35
% 3.09/1.44  Inferencing          : 0.13
% 3.09/1.44  Reduction            : 0.10
% 3.09/1.44  Demodulation         : 0.06
% 3.09/1.44  BG Simplification    : 0.02
% 3.09/1.45  Subsumption          : 0.07
% 3.09/1.45  Abstraction          : 0.02
% 3.09/1.45  MUC search           : 0.00
% 3.09/1.45  Cooper               : 0.00
% 3.09/1.45  Total                : 0.70
% 3.09/1.45  Index Insertion      : 0.00
% 3.09/1.45  Index Deletion       : 0.00
% 3.09/1.45  Index Matching       : 0.00
% 3.09/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
