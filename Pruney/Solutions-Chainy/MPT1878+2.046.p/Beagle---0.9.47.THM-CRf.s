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
% DateTime   : Thu Dec  3 10:30:03 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 139 expanded)
%              Number of leaves         :   38 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  166 ( 319 expanded)
%              Number of equality atoms :   35 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k4_tarski > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_32,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_26,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_68,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_20,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_116,plain,(
    ! [A_56] :
      ( r2_hidden('#skF_1'(A_56),A_56)
      | A_56 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_20])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,(
    ! [A_56] :
      ( m1_subset_1('#skF_1'(A_56),A_56)
      | A_56 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_116,c_16])).

tff(c_115,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_1'(A_14),A_14)
      | A_14 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_20])).

tff(c_147,plain,(
    ! [A_74,B_75] :
      ( k6_domain_1(A_74,B_75) = k1_tarski(B_75)
      | ~ m1_subset_1(B_75,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_158,plain,(
    ! [A_56] :
      ( k6_domain_1(A_56,'#skF_1'(A_56)) = k1_tarski('#skF_1'(A_56))
      | v1_xboole_0(A_56)
      | A_56 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_120,c_147])).

tff(c_233,plain,(
    ! [A_89,B_90] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_89),B_90),A_89)
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_603,plain,(
    ! [A_152] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_152))),A_152)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_152)),u1_struct_0(A_152))
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152)
      | v1_xboole_0(u1_struct_0(A_152))
      | u1_struct_0(A_152) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_233])).

tff(c_6,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_52] : k2_xboole_0(A_52,'#skF_4') = A_52 ),
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
    ! [A_7,B_8] :
      ( m1_subset_1(k1_tarski(A_7),k1_zfmisc_1(B_8))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

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

tff(c_441,plain,(
    ! [C_127,B_128,A_129] :
      ( C_127 = B_128
      | ~ r1_tarski(B_128,C_127)
      | ~ v2_tex_2(C_127,A_129)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ v3_tex_2(B_128,A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_443,plain,(
    ! [A_3,A_129] :
      ( A_3 = '#skF_4'
      | ~ v2_tex_2(A_3,A_129)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ v3_tex_2('#skF_4',A_129)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_81,c_441])).

tff(c_447,plain,(
    ! [A_130,A_131] :
      ( A_130 = '#skF_4'
      | ~ v2_tex_2(A_130,A_131)
      | ~ m1_subset_1(A_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v3_tex_2('#skF_4',A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_443])).

tff(c_466,plain,(
    ! [A_7,A_131] :
      ( k1_tarski(A_7) = '#skF_4'
      | ~ v2_tex_2(k1_tarski(A_7),A_131)
      | ~ v3_tex_2('#skF_4',A_131)
      | ~ l1_pre_topc(A_131)
      | ~ r2_hidden(A_7,u1_struct_0(A_131)) ) ),
    inference(resolution,[status(thm)],[c_14,c_447])).

tff(c_481,plain,(
    ! [A_7,A_131] :
      ( ~ v2_tex_2(k1_tarski(A_7),A_131)
      | ~ v3_tex_2('#skF_4',A_131)
      | ~ l1_pre_topc(A_131)
      | ~ r2_hidden(A_7,u1_struct_0(A_131)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_466])).

tff(c_654,plain,(
    ! [A_171] :
      ( ~ v3_tex_2('#skF_4',A_171)
      | ~ r2_hidden('#skF_1'(u1_struct_0(A_171)),u1_struct_0(A_171))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_171)),u1_struct_0(A_171))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171)
      | v1_xboole_0(u1_struct_0(A_171))
      | u1_struct_0(A_171) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_603,c_481])).

tff(c_659,plain,(
    ! [A_172] :
      ( ~ v3_tex_2('#skF_4',A_172)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_172)),u1_struct_0(A_172))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172)
      | v1_xboole_0(u1_struct_0(A_172))
      | u1_struct_0(A_172) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_115,c_654])).

tff(c_664,plain,(
    ! [A_173] :
      ( ~ v3_tex_2('#skF_4',A_173)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173)
      | v1_xboole_0(u1_struct_0(A_173))
      | u1_struct_0(A_173) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_120,c_659])).

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

tff(c_677,plain,(
    ! [A_176] :
      ( ~ v3_tex_2('#skF_4',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176)
      | u1_struct_0(A_176) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_664,c_78])).

tff(c_683,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_677])).

tff(c_687,plain,
    ( v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_683])).

tff(c_688,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_687])).

tff(c_28,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(u1_struct_0(A_25))
      | ~ l1_struct_0(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_729,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_28])).

tff(c_761,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_729])).

tff(c_762,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_761])).

tff(c_766,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_762])).

tff(c_770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:21:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.64  
% 3.31/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.65  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k4_tarski > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.31/1.65  
% 3.31/1.65  %Foreground sorts:
% 3.31/1.65  
% 3.31/1.65  
% 3.31/1.65  %Background operators:
% 3.31/1.65  
% 3.31/1.65  
% 3.31/1.65  %Foreground operators:
% 3.31/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.31/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.31/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.31/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.31/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.31/1.65  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.31/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.65  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.31/1.65  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.31/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.31/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.31/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.31/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.65  
% 3.31/1.66  tff(f_134, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 3.31/1.66  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.31/1.66  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.31/1.66  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.31/1.66  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.31/1.66  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.31/1.66  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 3.31/1.66  tff(f_32, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.31/1.66  tff(f_37, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.31/1.66  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.31/1.66  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.31/1.66  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.31/1.66  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.31/1.66  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.31/1.66  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.31/1.66  tff(c_26, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.31/1.66  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.31/1.66  tff(c_50, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.31/1.66  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.31/1.66  tff(c_46, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.31/1.66  tff(c_68, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.31/1.66  tff(c_77, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_68])).
% 3.31/1.66  tff(c_20, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.31/1.66  tff(c_116, plain, (![A_56]: (r2_hidden('#skF_1'(A_56), A_56) | A_56='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_20])).
% 3.31/1.66  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.31/1.66  tff(c_120, plain, (![A_56]: (m1_subset_1('#skF_1'(A_56), A_56) | A_56='#skF_4')), inference(resolution, [status(thm)], [c_116, c_16])).
% 3.31/1.66  tff(c_115, plain, (![A_14]: (r2_hidden('#skF_1'(A_14), A_14) | A_14='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_20])).
% 3.31/1.66  tff(c_147, plain, (![A_74, B_75]: (k6_domain_1(A_74, B_75)=k1_tarski(B_75) | ~m1_subset_1(B_75, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.31/1.66  tff(c_158, plain, (![A_56]: (k6_domain_1(A_56, '#skF_1'(A_56))=k1_tarski('#skF_1'(A_56)) | v1_xboole_0(A_56) | A_56='#skF_4')), inference(resolution, [status(thm)], [c_120, c_147])).
% 3.31/1.66  tff(c_233, plain, (![A_89, B_90]: (v2_tex_2(k6_domain_1(u1_struct_0(A_89), B_90), A_89) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.31/1.66  tff(c_603, plain, (![A_152]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_152))), A_152) | ~m1_subset_1('#skF_1'(u1_struct_0(A_152)), u1_struct_0(A_152)) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152) | v1_xboole_0(u1_struct_0(A_152)) | u1_struct_0(A_152)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_158, c_233])).
% 3.31/1.66  tff(c_6, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.66  tff(c_100, plain, (![A_52]: (k2_xboole_0(A_52, '#skF_4')=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_6])).
% 3.31/1.66  tff(c_10, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.66  tff(c_92, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_10])).
% 3.31/1.66  tff(c_107, plain, (![A_4]: (k1_tarski(A_4)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_100, c_92])).
% 3.31/1.66  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(k1_tarski(A_7), k1_zfmisc_1(B_8)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.31/1.66  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.31/1.66  tff(c_79, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_12])).
% 3.31/1.66  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.31/1.66  tff(c_81, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_8])).
% 3.31/1.66  tff(c_441, plain, (![C_127, B_128, A_129]: (C_127=B_128 | ~r1_tarski(B_128, C_127) | ~v2_tex_2(C_127, A_129) | ~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_129))) | ~v3_tex_2(B_128, A_129) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.31/1.66  tff(c_443, plain, (![A_3, A_129]: (A_3='#skF_4' | ~v2_tex_2(A_3, A_129) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_129))) | ~v3_tex_2('#skF_4', A_129) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(resolution, [status(thm)], [c_81, c_441])).
% 3.31/1.66  tff(c_447, plain, (![A_130, A_131]: (A_130='#skF_4' | ~v2_tex_2(A_130, A_131) | ~m1_subset_1(A_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~v3_tex_2('#skF_4', A_131) | ~l1_pre_topc(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_443])).
% 3.31/1.66  tff(c_466, plain, (![A_7, A_131]: (k1_tarski(A_7)='#skF_4' | ~v2_tex_2(k1_tarski(A_7), A_131) | ~v3_tex_2('#skF_4', A_131) | ~l1_pre_topc(A_131) | ~r2_hidden(A_7, u1_struct_0(A_131)))), inference(resolution, [status(thm)], [c_14, c_447])).
% 3.31/1.66  tff(c_481, plain, (![A_7, A_131]: (~v2_tex_2(k1_tarski(A_7), A_131) | ~v3_tex_2('#skF_4', A_131) | ~l1_pre_topc(A_131) | ~r2_hidden(A_7, u1_struct_0(A_131)))), inference(negUnitSimplification, [status(thm)], [c_107, c_466])).
% 3.31/1.66  tff(c_654, plain, (![A_171]: (~v3_tex_2('#skF_4', A_171) | ~r2_hidden('#skF_1'(u1_struct_0(A_171)), u1_struct_0(A_171)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_171)), u1_struct_0(A_171)) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171) | v1_xboole_0(u1_struct_0(A_171)) | u1_struct_0(A_171)='#skF_4')), inference(resolution, [status(thm)], [c_603, c_481])).
% 3.31/1.66  tff(c_659, plain, (![A_172]: (~v3_tex_2('#skF_4', A_172) | ~m1_subset_1('#skF_1'(u1_struct_0(A_172)), u1_struct_0(A_172)) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172) | v1_xboole_0(u1_struct_0(A_172)) | u1_struct_0(A_172)='#skF_4')), inference(resolution, [status(thm)], [c_115, c_654])).
% 3.31/1.66  tff(c_664, plain, (![A_173]: (~v3_tex_2('#skF_4', A_173) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173) | v1_xboole_0(u1_struct_0(A_173)) | u1_struct_0(A_173)='#skF_4')), inference(resolution, [status(thm)], [c_120, c_659])).
% 3.31/1.66  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.31/1.66  tff(c_78, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_4])).
% 3.31/1.66  tff(c_677, plain, (![A_176]: (~v3_tex_2('#skF_4', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176) | u1_struct_0(A_176)='#skF_4')), inference(resolution, [status(thm)], [c_664, c_78])).
% 3.31/1.66  tff(c_683, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_677])).
% 3.31/1.66  tff(c_687, plain, (v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_683])).
% 3.31/1.66  tff(c_688, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_687])).
% 3.31/1.66  tff(c_28, plain, (![A_25]: (~v1_xboole_0(u1_struct_0(A_25)) | ~l1_struct_0(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.31/1.66  tff(c_729, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_688, c_28])).
% 3.31/1.66  tff(c_761, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_729])).
% 3.31/1.66  tff(c_762, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_761])).
% 3.31/1.66  tff(c_766, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_762])).
% 3.31/1.66  tff(c_770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_766])).
% 3.31/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.66  
% 3.31/1.66  Inference rules
% 3.31/1.66  ----------------------
% 3.31/1.66  #Ref     : 0
% 3.31/1.66  #Sup     : 145
% 3.31/1.66  #Fact    : 0
% 3.31/1.66  #Define  : 0
% 3.31/1.66  #Split   : 0
% 3.31/1.66  #Chain   : 0
% 3.31/1.66  #Close   : 0
% 3.31/1.66  
% 3.31/1.66  Ordering : KBO
% 3.31/1.66  
% 3.31/1.66  Simplification rules
% 3.31/1.66  ----------------------
% 3.31/1.66  #Subsume      : 5
% 3.31/1.66  #Demod        : 53
% 3.31/1.66  #Tautology    : 38
% 3.31/1.66  #SimpNegUnit  : 8
% 3.31/1.66  #BackRed      : 5
% 3.31/1.66  
% 3.31/1.66  #Partial instantiations: 0
% 3.31/1.66  #Strategies tried      : 1
% 3.31/1.66  
% 3.31/1.66  Timing (in seconds)
% 3.31/1.66  ----------------------
% 3.31/1.67  Preprocessing        : 0.34
% 3.31/1.67  Parsing              : 0.18
% 3.31/1.67  CNF conversion       : 0.02
% 3.31/1.67  Main loop            : 0.53
% 3.31/1.67  Inferencing          : 0.23
% 3.31/1.67  Reduction            : 0.14
% 3.31/1.67  Demodulation         : 0.09
% 3.31/1.67  BG Simplification    : 0.03
% 3.31/1.67  Subsumption          : 0.10
% 3.31/1.67  Abstraction          : 0.03
% 3.31/1.67  MUC search           : 0.00
% 3.31/1.67  Cooper               : 0.00
% 3.31/1.67  Total                : 0.90
% 3.31/1.67  Index Insertion      : 0.00
% 3.31/1.67  Index Deletion       : 0.00
% 3.31/1.67  Index Matching       : 0.00
% 3.31/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
