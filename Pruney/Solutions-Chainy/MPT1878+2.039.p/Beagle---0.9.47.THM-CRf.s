%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:02 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 131 expanded)
%              Number of leaves         :   38 (  60 expanded)
%              Depth                    :   20
%              Number of atoms          :  172 ( 306 expanded)
%              Number of equality atoms :   39 (  63 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_24,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

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

tff(c_18,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_116,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_1'(A_60),A_60)
      | A_60 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_18])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_120,plain,(
    ! [A_60] :
      ( m1_subset_1('#skF_1'(A_60),A_60)
      | A_60 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_116,c_14])).

tff(c_44,plain,(
    ! [A_42,B_44] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_42),B_44),A_42)
      | ~ m1_subset_1(B_44,u1_struct_0(A_42))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k6_domain_1(A_28,B_29),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

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

tff(c_610,plain,(
    ! [C_129,B_130,A_131] :
      ( C_129 = B_130
      | ~ r1_tarski(B_130,C_129)
      | ~ v2_tex_2(C_129,A_131)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v3_tex_2(B_130,A_131)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_612,plain,(
    ! [A_3,A_131] :
      ( A_3 = '#skF_4'
      | ~ v2_tex_2(A_3,A_131)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v3_tex_2('#skF_4',A_131)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_81,c_610])).

tff(c_816,plain,(
    ! [A_140,A_141] :
      ( A_140 = '#skF_4'
      | ~ v2_tex_2(A_140,A_141)
      | ~ m1_subset_1(A_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v3_tex_2('#skF_4',A_141)
      | ~ l1_pre_topc(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_612])).

tff(c_1690,plain,(
    ! [A_178,B_179] :
      ( k6_domain_1(u1_struct_0(A_178),B_179) = '#skF_4'
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_178),B_179),A_178)
      | ~ v3_tex_2('#skF_4',A_178)
      | ~ l1_pre_topc(A_178)
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | v1_xboole_0(u1_struct_0(A_178)) ) ),
    inference(resolution,[status(thm)],[c_28,c_816])).

tff(c_1711,plain,(
    ! [A_180,B_181] :
      ( k6_domain_1(u1_struct_0(A_180),B_181) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_180)
      | v1_xboole_0(u1_struct_0(A_180))
      | ~ m1_subset_1(B_181,u1_struct_0(A_180))
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(resolution,[status(thm)],[c_44,c_1690])).

tff(c_1732,plain,(
    ! [A_182] :
      ( k6_domain_1(u1_struct_0(A_182),'#skF_1'(u1_struct_0(A_182))) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_182)
      | v1_xboole_0(u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182)
      | u1_struct_0(A_182) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_120,c_1711])).

tff(c_123,plain,(
    ! [A_63,B_64] :
      ( k6_domain_1(A_63,B_64) = k1_tarski(B_64)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_130,plain,(
    ! [A_60] :
      ( k6_domain_1(A_60,'#skF_1'(A_60)) = k1_tarski('#skF_1'(A_60))
      | v1_xboole_0(A_60)
      | A_60 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_120,c_123])).

tff(c_1762,plain,(
    ! [A_182] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_182))) = '#skF_4'
      | v1_xboole_0(u1_struct_0(A_182))
      | u1_struct_0(A_182) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_182)
      | v1_xboole_0(u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182)
      | u1_struct_0(A_182) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_130])).

tff(c_1775,plain,(
    ! [A_182] :
      ( v1_xboole_0(u1_struct_0(A_182))
      | u1_struct_0(A_182) = '#skF_4'
      | ~ v3_tex_2('#skF_4',A_182)
      | v1_xboole_0(u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182)
      | u1_struct_0(A_182) = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1762])).

tff(c_1794,plain,(
    ! [A_184] :
      ( ~ v3_tex_2('#skF_4',A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | u1_struct_0(A_184) = '#skF_4'
      | v1_xboole_0(u1_struct_0(A_184)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1775])).

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

tff(c_1803,plain,(
    ! [A_185] :
      ( ~ v3_tex_2('#skF_4',A_185)
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185)
      | u1_struct_0(A_185) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1794,c_78])).

tff(c_1809,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_1803])).

tff(c_1813,plain,
    ( v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1809])).

tff(c_1814,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1813])).

tff(c_26,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(u1_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1858,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_26])).

tff(c_1892,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1858])).

tff(c_1893,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1892])).

tff(c_1898,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1893])).

tff(c_1902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1898])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n019.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 14:46:37 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.62  
% 3.91/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.62  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.91/1.62  
% 3.91/1.62  %Foreground sorts:
% 3.91/1.62  
% 3.91/1.62  
% 3.91/1.62  %Background operators:
% 3.91/1.62  
% 3.91/1.62  
% 3.91/1.62  %Foreground operators:
% 3.91/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.91/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.91/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.91/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.62  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.91/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.91/1.62  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.91/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.62  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.91/1.62  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.91/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.91/1.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.91/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.91/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.91/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.91/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.91/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.91/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.91/1.62  
% 4.29/1.64  tff(f_137, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 4.29/1.64  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.29/1.64  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.29/1.64  tff(f_32, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.29/1.64  tff(f_37, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.29/1.64  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.29/1.64  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.29/1.64  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 4.29/1.64  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.29/1.64  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.29/1.64  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.29/1.64  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.29/1.64  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.29/1.64  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.29/1.64  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.29/1.64  tff(c_24, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.29/1.64  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.29/1.64  tff(c_50, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.29/1.64  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.29/1.64  tff(c_46, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.29/1.64  tff(c_68, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.29/1.64  tff(c_77, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_68])).
% 4.29/1.64  tff(c_6, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.29/1.64  tff(c_100, plain, (![A_56]: (k2_xboole_0(A_56, '#skF_4')=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_6])).
% 4.29/1.64  tff(c_10, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.29/1.64  tff(c_92, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_10])).
% 4.29/1.64  tff(c_107, plain, (![A_4]: (k1_tarski(A_4)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_100, c_92])).
% 4.29/1.64  tff(c_18, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.29/1.64  tff(c_116, plain, (![A_60]: (r2_hidden('#skF_1'(A_60), A_60) | A_60='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_18])).
% 4.29/1.64  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.29/1.64  tff(c_120, plain, (![A_60]: (m1_subset_1('#skF_1'(A_60), A_60) | A_60='#skF_4')), inference(resolution, [status(thm)], [c_116, c_14])).
% 4.29/1.64  tff(c_44, plain, (![A_42, B_44]: (v2_tex_2(k6_domain_1(u1_struct_0(A_42), B_44), A_42) | ~m1_subset_1(B_44, u1_struct_0(A_42)) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.29/1.64  tff(c_28, plain, (![A_28, B_29]: (m1_subset_1(k6_domain_1(A_28, B_29), k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.29/1.64  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.29/1.64  tff(c_79, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_12])).
% 4.29/1.64  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.29/1.64  tff(c_81, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_8])).
% 4.29/1.64  tff(c_610, plain, (![C_129, B_130, A_131]: (C_129=B_130 | ~r1_tarski(B_130, C_129) | ~v2_tex_2(C_129, A_131) | ~m1_subset_1(C_129, k1_zfmisc_1(u1_struct_0(A_131))) | ~v3_tex_2(B_130, A_131) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.29/1.64  tff(c_612, plain, (![A_3, A_131]: (A_3='#skF_4' | ~v2_tex_2(A_3, A_131) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_131))) | ~v3_tex_2('#skF_4', A_131) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_81, c_610])).
% 4.29/1.64  tff(c_816, plain, (![A_140, A_141]: (A_140='#skF_4' | ~v2_tex_2(A_140, A_141) | ~m1_subset_1(A_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~v3_tex_2('#skF_4', A_141) | ~l1_pre_topc(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_612])).
% 4.29/1.64  tff(c_1690, plain, (![A_178, B_179]: (k6_domain_1(u1_struct_0(A_178), B_179)='#skF_4' | ~v2_tex_2(k6_domain_1(u1_struct_0(A_178), B_179), A_178) | ~v3_tex_2('#skF_4', A_178) | ~l1_pre_topc(A_178) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | v1_xboole_0(u1_struct_0(A_178)))), inference(resolution, [status(thm)], [c_28, c_816])).
% 4.29/1.64  tff(c_1711, plain, (![A_180, B_181]: (k6_domain_1(u1_struct_0(A_180), B_181)='#skF_4' | ~v3_tex_2('#skF_4', A_180) | v1_xboole_0(u1_struct_0(A_180)) | ~m1_subset_1(B_181, u1_struct_0(A_180)) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(resolution, [status(thm)], [c_44, c_1690])).
% 4.29/1.64  tff(c_1732, plain, (![A_182]: (k6_domain_1(u1_struct_0(A_182), '#skF_1'(u1_struct_0(A_182)))='#skF_4' | ~v3_tex_2('#skF_4', A_182) | v1_xboole_0(u1_struct_0(A_182)) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182) | u1_struct_0(A_182)='#skF_4')), inference(resolution, [status(thm)], [c_120, c_1711])).
% 4.29/1.64  tff(c_123, plain, (![A_63, B_64]: (k6_domain_1(A_63, B_64)=k1_tarski(B_64) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.29/1.64  tff(c_130, plain, (![A_60]: (k6_domain_1(A_60, '#skF_1'(A_60))=k1_tarski('#skF_1'(A_60)) | v1_xboole_0(A_60) | A_60='#skF_4')), inference(resolution, [status(thm)], [c_120, c_123])).
% 4.29/1.64  tff(c_1762, plain, (![A_182]: (k1_tarski('#skF_1'(u1_struct_0(A_182)))='#skF_4' | v1_xboole_0(u1_struct_0(A_182)) | u1_struct_0(A_182)='#skF_4' | ~v3_tex_2('#skF_4', A_182) | v1_xboole_0(u1_struct_0(A_182)) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182) | u1_struct_0(A_182)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1732, c_130])).
% 4.29/1.64  tff(c_1775, plain, (![A_182]: (v1_xboole_0(u1_struct_0(A_182)) | u1_struct_0(A_182)='#skF_4' | ~v3_tex_2('#skF_4', A_182) | v1_xboole_0(u1_struct_0(A_182)) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182) | u1_struct_0(A_182)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_107, c_1762])).
% 4.29/1.64  tff(c_1794, plain, (![A_184]: (~v3_tex_2('#skF_4', A_184) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184) | u1_struct_0(A_184)='#skF_4' | v1_xboole_0(u1_struct_0(A_184)))), inference(factorization, [status(thm), theory('equality')], [c_1775])).
% 4.29/1.64  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.29/1.64  tff(c_78, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_4])).
% 4.29/1.64  tff(c_1803, plain, (![A_185]: (~v3_tex_2('#skF_4', A_185) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185) | v2_struct_0(A_185) | u1_struct_0(A_185)='#skF_4')), inference(resolution, [status(thm)], [c_1794, c_78])).
% 4.29/1.64  tff(c_1809, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_1803])).
% 4.29/1.64  tff(c_1813, plain, (v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1809])).
% 4.29/1.64  tff(c_1814, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_1813])).
% 4.29/1.64  tff(c_26, plain, (![A_27]: (~v1_xboole_0(u1_struct_0(A_27)) | ~l1_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.29/1.64  tff(c_1858, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1814, c_26])).
% 4.29/1.64  tff(c_1892, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1858])).
% 4.29/1.64  tff(c_1893, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_1892])).
% 4.29/1.64  tff(c_1898, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1893])).
% 4.29/1.64  tff(c_1902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1898])).
% 4.29/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.64  
% 4.29/1.64  Inference rules
% 4.29/1.64  ----------------------
% 4.29/1.64  #Ref     : 0
% 4.29/1.64  #Sup     : 409
% 4.29/1.64  #Fact    : 2
% 4.29/1.64  #Define  : 0
% 4.29/1.64  #Split   : 5
% 4.29/1.64  #Chain   : 0
% 4.29/1.64  #Close   : 0
% 4.29/1.64  
% 4.29/1.64  Ordering : KBO
% 4.29/1.64  
% 4.29/1.64  Simplification rules
% 4.29/1.64  ----------------------
% 4.29/1.64  #Subsume      : 43
% 4.29/1.64  #Demod        : 493
% 4.29/1.64  #Tautology    : 163
% 4.29/1.64  #SimpNegUnit  : 70
% 4.29/1.64  #BackRed      : 11
% 4.29/1.64  
% 4.29/1.64  #Partial instantiations: 0
% 4.29/1.64  #Strategies tried      : 1
% 4.29/1.64  
% 4.29/1.64  Timing (in seconds)
% 4.29/1.64  ----------------------
% 4.29/1.64  Preprocessing        : 0.35
% 4.29/1.64  Parsing              : 0.19
% 4.29/1.64  CNF conversion       : 0.02
% 4.29/1.64  Main loop            : 0.65
% 4.29/1.64  Inferencing          : 0.23
% 4.29/1.64  Reduction            : 0.20
% 4.29/1.64  Demodulation         : 0.13
% 4.29/1.64  BG Simplification    : 0.03
% 4.29/1.64  Subsumption          : 0.15
% 4.29/1.64  Abstraction          : 0.03
% 4.29/1.64  MUC search           : 0.00
% 4.29/1.64  Cooper               : 0.00
% 4.29/1.64  Total                : 1.03
% 4.29/1.64  Index Insertion      : 0.00
% 4.29/1.64  Index Deletion       : 0.00
% 4.29/1.64  Index Matching       : 0.00
% 4.29/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
