%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:02 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 130 expanded)
%              Number of leaves         :   37 (  59 expanded)
%              Depth                    :   20
%              Number of atoms          :  169 ( 300 expanded)
%              Number of equality atoms :   38 (  61 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

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
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_106,plain,(
    ! [A_2] :
      ( m1_subset_1('#skF_1'(A_2),A_2)
      | A_2 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_100,c_102])).

tff(c_40,plain,(
    ! [A_30,B_32] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_30),B_32),A_30)
      | ~ m1_subset_1(B_32,u1_struct_0(A_30))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k6_domain_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

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

tff(c_634,plain,(
    ! [C_97,B_98,A_99] :
      ( C_97 = B_98
      | ~ r1_tarski(B_98,C_97)
      | ~ v2_tex_2(C_97,A_99)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ v3_tex_2(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_636,plain,(
    ! [A_5,A_99] :
      ( A_5 = '#skF_4'
      | ~ v2_tex_2(A_5,A_99)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ v3_tex_2('#skF_4',A_99)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_65,c_634])).

tff(c_736,plain,(
    ! [A_105,A_106] :
      ( A_105 = '#skF_4'
      | ~ v2_tex_2(A_105,A_106)
      | ~ m1_subset_1(A_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v3_tex_2('#skF_4',A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_636])).

tff(c_1625,plain,(
    ! [A_143,B_144] :
      ( k6_domain_1(u1_struct_0(A_143),B_144) = '#skF_4'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_143),B_144),A_143)
      | ~ v3_tex_2('#skF_4',A_143)
      | ~ l1_pre_topc(A_143)
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | v1_xboole_0(u1_struct_0(A_143)) ) ),
    inference(resolution,[status(thm)],[c_24,c_736])).

tff(c_1646,plain,(
    ! [A_145,B_146] :
      ( k6_domain_1(u1_struct_0(A_145),B_146) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_145)
      | v1_xboole_0(u1_struct_0(A_145))
      | ~ m1_subset_1(B_146,u1_struct_0(A_145))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_40,c_1625])).

tff(c_1669,plain,(
    ! [A_147] :
      ( k6_domain_1(u1_struct_0(A_147),'#skF_1'(u1_struct_0(A_147))) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_147)
      | v1_xboole_0(u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | u1_struct_0(A_147) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_106,c_1646])).

tff(c_123,plain,(
    ! [A_54,B_55] :
      ( k6_domain_1(A_54,B_55) = k1_tarski(B_55)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_130,plain,(
    ! [A_2] :
      ( k6_domain_1(A_2,'#skF_1'(A_2)) = k1_tarski('#skF_1'(A_2))
      | v1_xboole_0(A_2)
      | A_2 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_106,c_123])).

tff(c_1696,plain,(
    ! [A_147] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_147))) = '#skF_4'
      | v1_xboole_0(u1_struct_0(A_147))
      | u1_struct_0(A_147) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_147)
      | v1_xboole_0(u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | u1_struct_0(A_147) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1669,c_130])).

tff(c_1709,plain,(
    ! [A_147] :
      ( v1_xboole_0(u1_struct_0(A_147))
      | u1_struct_0(A_147) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_147)
      | v1_xboole_0(u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | u1_struct_0(A_147) = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1696])).

tff(c_1728,plain,(
    ! [A_149] :
      ( ~ v3_tex_2('#skF_4',A_149)
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149)
      | u1_struct_0(A_149) = '#skF_4'
      | v1_xboole_0(u1_struct_0(A_149)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1709])).

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

tff(c_1737,plain,(
    ! [A_150] :
      ( ~ v3_tex_2('#skF_4',A_150)
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150)
      | u1_struct_0(A_150) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1728,c_64])).

tff(c_1743,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_1737])).

tff(c_1747,plain,
    ( v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1743])).

tff(c_1748,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1747])).

tff(c_22,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1789,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1748,c_22])).

tff(c_1821,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1789])).

tff(c_1822,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1821])).

tff(c_1848,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1822])).

tff(c_1852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.72  
% 4.19/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.73  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.19/1.73  
% 4.19/1.73  %Foreground sorts:
% 4.19/1.73  
% 4.19/1.73  
% 4.19/1.73  %Background operators:
% 4.19/1.73  
% 4.19/1.73  
% 4.19/1.73  %Foreground operators:
% 4.19/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.19/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.19/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.19/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.19/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.19/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.19/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.19/1.73  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.19/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.19/1.73  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.19/1.73  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.19/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.19/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.19/1.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.19/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.19/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.19/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.19/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.19/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.19/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.19/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.19/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.19/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.19/1.73  
% 4.19/1.74  tff(f_129, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 4.19/1.74  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.19/1.74  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.19/1.74  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.19/1.74  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.19/1.74  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.19/1.74  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.19/1.74  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 4.19/1.74  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.19/1.74  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.19/1.74  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.19/1.74  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.19/1.74  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.19/1.74  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.19/1.74  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.19/1.74  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.19/1.74  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.19/1.74  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.19/1.74  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.19/1.74  tff(c_42, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.19/1.74  tff(c_54, plain, (![A_35]: (k1_xboole_0=A_35 | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.19/1.74  tff(c_63, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_54])).
% 4.19/1.74  tff(c_8, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.19/1.74  tff(c_76, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_8])).
% 4.19/1.74  tff(c_12, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.19/1.74  tff(c_94, plain, (![A_41, B_42]: (k2_xboole_0(k1_tarski(A_41), B_42)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_12])).
% 4.19/1.74  tff(c_98, plain, (![A_41]: (k1_tarski(A_41)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_76, c_94])).
% 4.19/1.74  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.19/1.74  tff(c_100, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_6])).
% 4.19/1.74  tff(c_102, plain, (![A_45, B_46]: (m1_subset_1(A_45, B_46) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.19/1.74  tff(c_106, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), A_2) | A_2='#skF_4')), inference(resolution, [status(thm)], [c_100, c_102])).
% 4.19/1.74  tff(c_40, plain, (![A_30, B_32]: (v2_tex_2(k6_domain_1(u1_struct_0(A_30), B_32), A_30) | ~m1_subset_1(B_32, u1_struct_0(A_30)) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.19/1.74  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k6_domain_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.19/1.74  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.19/1.74  tff(c_73, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_14])).
% 4.19/1.74  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.19/1.74  tff(c_65, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_10])).
% 4.19/1.74  tff(c_634, plain, (![C_97, B_98, A_99]: (C_97=B_98 | ~r1_tarski(B_98, C_97) | ~v2_tex_2(C_97, A_99) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_99))) | ~v3_tex_2(B_98, A_99) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.19/1.74  tff(c_636, plain, (![A_5, A_99]: (A_5='#skF_4' | ~v2_tex_2(A_5, A_99) | ~m1_subset_1(A_5, k1_zfmisc_1(u1_struct_0(A_99))) | ~v3_tex_2('#skF_4', A_99) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_65, c_634])).
% 4.19/1.74  tff(c_736, plain, (![A_105, A_106]: (A_105='#skF_4' | ~v2_tex_2(A_105, A_106) | ~m1_subset_1(A_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~v3_tex_2('#skF_4', A_106) | ~l1_pre_topc(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_636])).
% 4.19/1.74  tff(c_1625, plain, (![A_143, B_144]: (k6_domain_1(u1_struct_0(A_143), B_144)='#skF_4' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_143), B_144), A_143) | ~v3_tex_2('#skF_4', A_143) | ~l1_pre_topc(A_143) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | v1_xboole_0(u1_struct_0(A_143)))), inference(resolution, [status(thm)], [c_24, c_736])).
% 4.19/1.74  tff(c_1646, plain, (![A_145, B_146]: (k6_domain_1(u1_struct_0(A_145), B_146)='#skF_4' | ~v3_tex_2('#skF_4', A_145) | v1_xboole_0(u1_struct_0(A_145)) | ~m1_subset_1(B_146, u1_struct_0(A_145)) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(resolution, [status(thm)], [c_40, c_1625])).
% 4.19/1.74  tff(c_1669, plain, (![A_147]: (k6_domain_1(u1_struct_0(A_147), '#skF_1'(u1_struct_0(A_147)))='#skF_4' | ~v3_tex_2('#skF_4', A_147) | v1_xboole_0(u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | u1_struct_0(A_147)='#skF_4')), inference(resolution, [status(thm)], [c_106, c_1646])).
% 4.19/1.74  tff(c_123, plain, (![A_54, B_55]: (k6_domain_1(A_54, B_55)=k1_tarski(B_55) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.19/1.74  tff(c_130, plain, (![A_2]: (k6_domain_1(A_2, '#skF_1'(A_2))=k1_tarski('#skF_1'(A_2)) | v1_xboole_0(A_2) | A_2='#skF_4')), inference(resolution, [status(thm)], [c_106, c_123])).
% 4.19/1.74  tff(c_1696, plain, (![A_147]: (k1_tarski('#skF_1'(u1_struct_0(A_147)))='#skF_4' | v1_xboole_0(u1_struct_0(A_147)) | u1_struct_0(A_147)='#skF_4' | ~v3_tex_2('#skF_4', A_147) | v1_xboole_0(u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | u1_struct_0(A_147)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1669, c_130])).
% 4.19/1.74  tff(c_1709, plain, (![A_147]: (v1_xboole_0(u1_struct_0(A_147)) | u1_struct_0(A_147)='#skF_4' | ~v3_tex_2('#skF_4', A_147) | v1_xboole_0(u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | u1_struct_0(A_147)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_98, c_1696])).
% 4.19/1.74  tff(c_1728, plain, (![A_149]: (~v3_tex_2('#skF_4', A_149) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149) | u1_struct_0(A_149)='#skF_4' | v1_xboole_0(u1_struct_0(A_149)))), inference(factorization, [status(thm), theory('equality')], [c_1709])).
% 4.19/1.74  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.19/1.74  tff(c_64, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_4])).
% 4.19/1.74  tff(c_1737, plain, (![A_150]: (~v3_tex_2('#skF_4', A_150) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150) | u1_struct_0(A_150)='#skF_4')), inference(resolution, [status(thm)], [c_1728, c_64])).
% 4.19/1.74  tff(c_1743, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_42, c_1737])).
% 4.19/1.74  tff(c_1747, plain, (v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1743])).
% 4.19/1.74  tff(c_1748, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_1747])).
% 4.19/1.74  tff(c_22, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.19/1.74  tff(c_1789, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1748, c_22])).
% 4.19/1.74  tff(c_1821, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1789])).
% 4.19/1.74  tff(c_1822, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_1821])).
% 4.19/1.74  tff(c_1848, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1822])).
% 4.19/1.74  tff(c_1852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1848])).
% 4.19/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.74  
% 4.19/1.74  Inference rules
% 4.19/1.74  ----------------------
% 4.19/1.74  #Ref     : 0
% 4.19/1.74  #Sup     : 401
% 4.19/1.74  #Fact    : 2
% 4.19/1.74  #Define  : 0
% 4.19/1.74  #Split   : 5
% 4.19/1.74  #Chain   : 0
% 4.19/1.74  #Close   : 0
% 4.19/1.74  
% 4.19/1.74  Ordering : KBO
% 4.19/1.74  
% 4.19/1.74  Simplification rules
% 4.19/1.74  ----------------------
% 4.19/1.74  #Subsume      : 39
% 4.19/1.74  #Demod        : 487
% 4.19/1.74  #Tautology    : 161
% 4.19/1.74  #SimpNegUnit  : 66
% 4.19/1.74  #BackRed      : 9
% 4.19/1.74  
% 4.19/1.74  #Partial instantiations: 0
% 4.19/1.74  #Strategies tried      : 1
% 4.19/1.74  
% 4.19/1.74  Timing (in seconds)
% 4.19/1.74  ----------------------
% 4.19/1.74  Preprocessing        : 0.31
% 4.19/1.74  Parsing              : 0.16
% 4.19/1.74  CNF conversion       : 0.02
% 4.19/1.74  Main loop            : 0.67
% 4.19/1.74  Inferencing          : 0.23
% 4.19/1.75  Reduction            : 0.21
% 4.19/1.75  Demodulation         : 0.14
% 4.19/1.75  BG Simplification    : 0.03
% 4.19/1.75  Subsumption          : 0.16
% 4.19/1.75  Abstraction          : 0.03
% 4.19/1.75  MUC search           : 0.00
% 4.19/1.75  Cooper               : 0.00
% 4.19/1.75  Total                : 1.02
% 4.19/1.75  Index Insertion      : 0.00
% 4.19/1.75  Index Deletion       : 0.00
% 4.19/1.75  Index Matching       : 0.00
% 4.19/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
