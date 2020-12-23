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

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 102 expanded)
%              Number of leaves         :   37 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  146 ( 217 expanded)
%              Number of equality atoms :   18 (  27 expanded)
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

tff(f_122,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_106,axiom,(
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

tff(f_94,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_20,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_127,plain,(
    ! [A_58,B_59] :
      ( k6_domain_1(A_58,B_59) = k1_tarski(B_59)
      | ~ m1_subset_1(B_59,A_58)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_138,plain,(
    ! [A_6] :
      ( k6_domain_1(A_6,'#skF_1'(A_6)) = k1_tarski('#skF_1'(A_6))
      | v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_127])).

tff(c_172,plain,(
    ! [A_64,B_65] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_64),B_65),A_64)
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_176,plain,(
    ! [A_64] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_64))),A_64)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_64)),u1_struct_0(A_64))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64)
      | v1_xboole_0(u1_struct_0(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_172])).

tff(c_178,plain,(
    ! [A_64] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_64))),A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64)
      | v1_xboole_0(u1_struct_0(A_64)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_176])).

tff(c_44,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_61,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_61])).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_44] : k2_xboole_0(A_44,'#skF_4') = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_4])).

tff(c_8,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),B_5) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_85,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),B_5) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_8])).

tff(c_94,plain,(
    ! [A_4] : k1_tarski(A_4) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_85])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k1_tarski(A_9),k1_zfmisc_1(B_10))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_12])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_6])).

tff(c_488,plain,(
    ! [C_111,B_112,A_113] :
      ( C_111 = B_112
      | ~ r1_tarski(B_112,C_111)
      | ~ v2_tex_2(C_111,A_113)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ v3_tex_2(B_112,A_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_490,plain,(
    ! [A_3,A_113] :
      ( A_3 = '#skF_4'
      | ~ v2_tex_2(A_3,A_113)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ v3_tex_2('#skF_4',A_113)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_68,c_488])).

tff(c_494,plain,(
    ! [A_114,A_115] :
      ( A_114 = '#skF_4'
      | ~ v2_tex_2(A_114,A_115)
      | ~ m1_subset_1(A_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v3_tex_2('#skF_4',A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_490])).

tff(c_517,plain,(
    ! [A_9,A_115] :
      ( k1_tarski(A_9) = '#skF_4'
      | ~ v2_tex_2(k1_tarski(A_9),A_115)
      | ~ v3_tex_2('#skF_4',A_115)
      | ~ l1_pre_topc(A_115)
      | ~ r2_hidden(A_9,u1_struct_0(A_115)) ) ),
    inference(resolution,[status(thm)],[c_14,c_494])).

tff(c_537,plain,(
    ! [A_116,A_117] :
      ( ~ v2_tex_2(k1_tarski(A_116),A_117)
      | ~ v3_tex_2('#skF_4',A_117)
      | ~ l1_pre_topc(A_117)
      | ~ r2_hidden(A_116,u1_struct_0(A_117)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_517])).

tff(c_548,plain,(
    ! [A_121] :
      ( ~ v3_tex_2('#skF_4',A_121)
      | ~ r2_hidden('#skF_1'(u1_struct_0(A_121)),u1_struct_0(A_121))
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121)
      | v1_xboole_0(u1_struct_0(A_121)) ) ),
    inference(resolution,[status(thm)],[c_178,c_537])).

tff(c_551,plain,(
    ! [A_121] :
      ( ~ v3_tex_2('#skF_4',A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121)
      | v1_xboole_0(u1_struct_0(A_121))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_121)),u1_struct_0(A_121)) ) ),
    inference(resolution,[status(thm)],[c_16,c_548])).

tff(c_555,plain,(
    ! [A_122] :
      ( ~ v3_tex_2('#skF_4',A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122)
      | v1_xboole_0(u1_struct_0(A_122)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_551])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_564,plain,(
    ! [A_123] :
      ( ~ l1_struct_0(A_123)
      | ~ v3_tex_2('#skF_4',A_123)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_555,c_22])).

tff(c_570,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_564])).

tff(c_574,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_570])).

tff(c_575,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_574])).

tff(c_578,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_575])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.80/1.43  
% 2.80/1.43  %Foreground sorts:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Background operators:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Foreground operators:
% 2.80/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.80/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.80/1.43  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.80/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.43  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.80/1.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.80/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.80/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.43  
% 2.80/1.44  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 2.80/1.44  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.80/1.44  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.80/1.44  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.80/1.44  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.80/1.44  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 2.80/1.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.80/1.44  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.80/1.44  tff(f_36, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.80/1.44  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.80/1.44  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.80/1.44  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.80/1.44  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 2.80/1.44  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.80/1.44  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.80/1.44  tff(c_20, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.80/1.44  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.80/1.44  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.80/1.44  tff(c_40, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.80/1.44  tff(c_10, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.44  tff(c_16, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.80/1.44  tff(c_127, plain, (![A_58, B_59]: (k6_domain_1(A_58, B_59)=k1_tarski(B_59) | ~m1_subset_1(B_59, A_58) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.80/1.44  tff(c_138, plain, (![A_6]: (k6_domain_1(A_6, '#skF_1'(A_6))=k1_tarski('#skF_1'(A_6)) | v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_10, c_127])).
% 2.80/1.44  tff(c_172, plain, (![A_64, B_65]: (v2_tex_2(k6_domain_1(u1_struct_0(A_64), B_65), A_64) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.80/1.44  tff(c_176, plain, (![A_64]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_64))), A_64) | ~m1_subset_1('#skF_1'(u1_struct_0(A_64)), u1_struct_0(A_64)) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64) | v1_xboole_0(u1_struct_0(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_138, c_172])).
% 2.80/1.44  tff(c_178, plain, (![A_64]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_64))), A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64) | v1_xboole_0(u1_struct_0(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_176])).
% 2.80/1.44  tff(c_44, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.80/1.44  tff(c_61, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.44  tff(c_65, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_61])).
% 2.80/1.44  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.44  tff(c_87, plain, (![A_44]: (k2_xboole_0(A_44, '#skF_4')=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_65, c_4])).
% 2.80/1.44  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.80/1.44  tff(c_85, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_8])).
% 2.80/1.44  tff(c_94, plain, (![A_4]: (k1_tarski(A_4)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_87, c_85])).
% 2.80/1.44  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(k1_tarski(A_9), k1_zfmisc_1(B_10)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.80/1.44  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.44  tff(c_74, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_12])).
% 2.80/1.44  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.44  tff(c_68, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_6])).
% 2.80/1.44  tff(c_488, plain, (![C_111, B_112, A_113]: (C_111=B_112 | ~r1_tarski(B_112, C_111) | ~v2_tex_2(C_111, A_113) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_113))) | ~v3_tex_2(B_112, A_113) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.80/1.44  tff(c_490, plain, (![A_3, A_113]: (A_3='#skF_4' | ~v2_tex_2(A_3, A_113) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_113))) | ~v3_tex_2('#skF_4', A_113) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_68, c_488])).
% 2.80/1.44  tff(c_494, plain, (![A_114, A_115]: (A_114='#skF_4' | ~v2_tex_2(A_114, A_115) | ~m1_subset_1(A_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~v3_tex_2('#skF_4', A_115) | ~l1_pre_topc(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_490])).
% 2.80/1.44  tff(c_517, plain, (![A_9, A_115]: (k1_tarski(A_9)='#skF_4' | ~v2_tex_2(k1_tarski(A_9), A_115) | ~v3_tex_2('#skF_4', A_115) | ~l1_pre_topc(A_115) | ~r2_hidden(A_9, u1_struct_0(A_115)))), inference(resolution, [status(thm)], [c_14, c_494])).
% 2.80/1.44  tff(c_537, plain, (![A_116, A_117]: (~v2_tex_2(k1_tarski(A_116), A_117) | ~v3_tex_2('#skF_4', A_117) | ~l1_pre_topc(A_117) | ~r2_hidden(A_116, u1_struct_0(A_117)))), inference(negUnitSimplification, [status(thm)], [c_94, c_517])).
% 2.80/1.44  tff(c_548, plain, (![A_121]: (~v3_tex_2('#skF_4', A_121) | ~r2_hidden('#skF_1'(u1_struct_0(A_121)), u1_struct_0(A_121)) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121) | v1_xboole_0(u1_struct_0(A_121)))), inference(resolution, [status(thm)], [c_178, c_537])).
% 2.80/1.44  tff(c_551, plain, (![A_121]: (~v3_tex_2('#skF_4', A_121) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121) | v1_xboole_0(u1_struct_0(A_121)) | ~m1_subset_1('#skF_1'(u1_struct_0(A_121)), u1_struct_0(A_121)))), inference(resolution, [status(thm)], [c_16, c_548])).
% 2.80/1.44  tff(c_555, plain, (![A_122]: (~v3_tex_2('#skF_4', A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122) | v1_xboole_0(u1_struct_0(A_122)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_551])).
% 2.80/1.44  tff(c_22, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.80/1.44  tff(c_564, plain, (![A_123]: (~l1_struct_0(A_123) | ~v3_tex_2('#skF_4', A_123) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_555, c_22])).
% 2.80/1.44  tff(c_570, plain, (~l1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_564])).
% 2.80/1.44  tff(c_574, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_570])).
% 2.80/1.44  tff(c_575, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_574])).
% 2.80/1.44  tff(c_578, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_575])).
% 2.80/1.44  tff(c_582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_578])).
% 2.80/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.44  
% 2.80/1.44  Inference rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Ref     : 0
% 2.80/1.44  #Sup     : 108
% 2.80/1.44  #Fact    : 0
% 2.80/1.44  #Define  : 0
% 2.80/1.44  #Split   : 0
% 2.80/1.44  #Chain   : 0
% 2.80/1.44  #Close   : 0
% 2.80/1.44  
% 2.80/1.44  Ordering : KBO
% 2.80/1.44  
% 2.80/1.44  Simplification rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Subsume      : 2
% 2.80/1.44  #Demod        : 15
% 2.80/1.44  #Tautology    : 25
% 2.80/1.44  #SimpNegUnit  : 2
% 2.80/1.44  #BackRed      : 3
% 2.80/1.44  
% 2.80/1.44  #Partial instantiations: 0
% 2.80/1.44  #Strategies tried      : 1
% 2.80/1.44  
% 2.80/1.44  Timing (in seconds)
% 2.80/1.44  ----------------------
% 2.80/1.45  Preprocessing        : 0.31
% 2.80/1.45  Parsing              : 0.16
% 2.80/1.45  CNF conversion       : 0.02
% 2.80/1.45  Main loop            : 0.32
% 2.80/1.45  Inferencing          : 0.12
% 2.80/1.45  Reduction            : 0.09
% 2.80/1.45  Demodulation         : 0.06
% 2.80/1.45  BG Simplification    : 0.02
% 2.80/1.45  Subsumption          : 0.06
% 2.80/1.45  Abstraction          : 0.02
% 2.80/1.45  MUC search           : 0.00
% 2.80/1.45  Cooper               : 0.00
% 2.80/1.45  Total                : 0.66
% 2.80/1.45  Index Insertion      : 0.00
% 2.80/1.45  Index Deletion       : 0.00
% 2.80/1.45  Index Matching       : 0.00
% 2.80/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
