%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:03 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 138 expanded)
%              Number of leaves         :   40 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  166 ( 315 expanded)
%              Number of equality atoms :   37 (  63 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_115,axiom,(
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

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_24,plain,(
    ! [A_38] :
      ( l1_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_44,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_67,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_67])).

tff(c_22,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_107,plain,(
    ! [A_70] :
      ( r2_hidden('#skF_1'(A_70),A_70)
      | A_70 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_22])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_111,plain,(
    ! [A_70] :
      ( m1_subset_1('#skF_1'(A_70),A_70)
      | A_70 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_107,c_16])).

tff(c_123,plain,(
    ! [A_75,B_76] :
      ( k6_domain_1(A_75,B_76) = k1_tarski(B_76)
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_130,plain,(
    ! [A_70] :
      ( k6_domain_1(A_70,'#skF_1'(A_70)) = k1_tarski('#skF_1'(A_70))
      | v1_xboole_0(A_70)
      | A_70 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_111,c_123])).

tff(c_214,plain,(
    ! [A_95,B_96] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_95),B_96),A_95)
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_563,plain,(
    ! [A_169] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_169))),A_169)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_169)),u1_struct_0(A_169))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169)
      | v1_xboole_0(u1_struct_0(A_169))
      | u1_struct_0(A_169) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_214])).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_2] : k2_xboole_0(A_2,'#skF_4') = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),B_7) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,(
    ! [A_64,B_65] : k2_xboole_0(k1_tarski(A_64),B_65) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_10])).

tff(c_101,plain,(
    ! [A_64] : k1_tarski(A_64) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_97])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(k1_tarski(B_10),k1_zfmisc_1(A_9))
      | k1_xboole_0 = A_9
      | ~ m1_subset_1(B_10,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(k1_tarski(B_10),k1_zfmisc_1(A_9))
      | A_9 = '#skF_4'
      | ~ m1_subset_1(B_10,A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_14])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_12])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_6])).

tff(c_445,plain,(
    ! [C_136,B_137,A_138] :
      ( C_136 = B_137
      | ~ r1_tarski(B_137,C_136)
      | ~ v2_tex_2(C_136,A_138)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ v3_tex_2(B_137,A_138)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_447,plain,(
    ! [A_3,A_138] :
      ( A_3 = '#skF_4'
      | ~ v2_tex_2(A_3,A_138)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ v3_tex_2('#skF_4',A_138)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_75,c_445])).

tff(c_451,plain,(
    ! [A_139,A_140] :
      ( A_139 = '#skF_4'
      | ~ v2_tex_2(A_139,A_140)
      | ~ m1_subset_1(A_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ v3_tex_2('#skF_4',A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_447])).

tff(c_470,plain,(
    ! [B_10,A_140] :
      ( k1_tarski(B_10) = '#skF_4'
      | ~ v2_tex_2(k1_tarski(B_10),A_140)
      | ~ v3_tex_2('#skF_4',A_140)
      | ~ l1_pre_topc(A_140)
      | u1_struct_0(A_140) = '#skF_4'
      | ~ m1_subset_1(B_10,u1_struct_0(A_140)) ) ),
    inference(resolution,[status(thm)],[c_160,c_451])).

tff(c_485,plain,(
    ! [B_10,A_140] :
      ( ~ v2_tex_2(k1_tarski(B_10),A_140)
      | ~ v3_tex_2('#skF_4',A_140)
      | ~ l1_pre_topc(A_140)
      | u1_struct_0(A_140) = '#skF_4'
      | ~ m1_subset_1(B_10,u1_struct_0(A_140)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_470])).

tff(c_568,plain,(
    ! [A_170] :
      ( ~ v3_tex_2('#skF_4',A_170)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_170)),u1_struct_0(A_170))
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170)
      | v1_xboole_0(u1_struct_0(A_170))
      | u1_struct_0(A_170) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_563,c_485])).

tff(c_573,plain,(
    ! [A_171] :
      ( ~ v3_tex_2('#skF_4',A_171)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171)
      | v1_xboole_0(u1_struct_0(A_171))
      | u1_struct_0(A_171) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_111,c_568])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_2])).

tff(c_582,plain,(
    ! [A_172] :
      ( ~ v3_tex_2('#skF_4',A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172)
      | u1_struct_0(A_172) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_573,c_72])).

tff(c_588,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_582])).

tff(c_592,plain,
    ( v2_struct_0('#skF_3')
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_588])).

tff(c_593,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_592])).

tff(c_26,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_631,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_26])).

tff(c_661,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_631])).

tff(c_662,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_661])).

tff(c_666,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_662])).

tff(c_670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:26:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.43  
% 2.85/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.44  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.85/1.44  
% 2.85/1.44  %Foreground sorts:
% 2.85/1.44  
% 2.85/1.44  
% 2.85/1.44  %Background operators:
% 2.85/1.44  
% 2.85/1.44  
% 2.85/1.44  %Foreground operators:
% 2.85/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.85/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.85/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.85/1.44  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.85/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.44  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.85/1.44  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.85/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.85/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.85/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.85/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.85/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.85/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.85/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.85/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.44  
% 2.85/1.45  tff(f_143, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 2.85/1.45  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.85/1.45  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.85/1.45  tff(f_78, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.85/1.45  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.85/1.45  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.85/1.45  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 2.85/1.45  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.85/1.45  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.85/1.45  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.85/1.45  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.85/1.45  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.85/1.45  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 2.85/1.45  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.85/1.45  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.85/1.45  tff(c_24, plain, (![A_38]: (l1_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.85/1.45  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.85/1.45  tff(c_48, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.85/1.45  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.85/1.45  tff(c_44, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.85/1.45  tff(c_67, plain, (![A_60]: (k1_xboole_0=A_60 | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.85/1.45  tff(c_71, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_48, c_67])).
% 2.85/1.45  tff(c_22, plain, (![A_16]: (r2_hidden('#skF_1'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.85/1.45  tff(c_107, plain, (![A_70]: (r2_hidden('#skF_1'(A_70), A_70) | A_70='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_22])).
% 2.85/1.45  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.85/1.45  tff(c_111, plain, (![A_70]: (m1_subset_1('#skF_1'(A_70), A_70) | A_70='#skF_4')), inference(resolution, [status(thm)], [c_107, c_16])).
% 2.85/1.45  tff(c_123, plain, (![A_75, B_76]: (k6_domain_1(A_75, B_76)=k1_tarski(B_76) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.85/1.45  tff(c_130, plain, (![A_70]: (k6_domain_1(A_70, '#skF_1'(A_70))=k1_tarski('#skF_1'(A_70)) | v1_xboole_0(A_70) | A_70='#skF_4')), inference(resolution, [status(thm)], [c_111, c_123])).
% 2.85/1.45  tff(c_214, plain, (![A_95, B_96]: (v2_tex_2(k6_domain_1(u1_struct_0(A_95), B_96), A_95) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.85/1.45  tff(c_563, plain, (![A_169]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_169))), A_169) | ~m1_subset_1('#skF_1'(u1_struct_0(A_169)), u1_struct_0(A_169)) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169) | v1_xboole_0(u1_struct_0(A_169)) | u1_struct_0(A_169)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_130, c_214])).
% 2.85/1.45  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.45  tff(c_74, plain, (![A_2]: (k2_xboole_0(A_2, '#skF_4')=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_4])).
% 2.85/1.45  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.85/1.45  tff(c_97, plain, (![A_64, B_65]: (k2_xboole_0(k1_tarski(A_64), B_65)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_10])).
% 2.85/1.45  tff(c_101, plain, (![A_64]: (k1_tarski(A_64)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_74, c_97])).
% 2.85/1.45  tff(c_14, plain, (![B_10, A_9]: (m1_subset_1(k1_tarski(B_10), k1_zfmisc_1(A_9)) | k1_xboole_0=A_9 | ~m1_subset_1(B_10, A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.85/1.45  tff(c_160, plain, (![B_10, A_9]: (m1_subset_1(k1_tarski(B_10), k1_zfmisc_1(A_9)) | A_9='#skF_4' | ~m1_subset_1(B_10, A_9))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_14])).
% 2.85/1.45  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.85/1.45  tff(c_73, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_12])).
% 2.85/1.45  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.85/1.45  tff(c_75, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_6])).
% 2.85/1.45  tff(c_445, plain, (![C_136, B_137, A_138]: (C_136=B_137 | ~r1_tarski(B_137, C_136) | ~v2_tex_2(C_136, A_138) | ~m1_subset_1(C_136, k1_zfmisc_1(u1_struct_0(A_138))) | ~v3_tex_2(B_137, A_138) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.85/1.45  tff(c_447, plain, (![A_3, A_138]: (A_3='#skF_4' | ~v2_tex_2(A_3, A_138) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_138))) | ~v3_tex_2('#skF_4', A_138) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_75, c_445])).
% 2.85/1.45  tff(c_451, plain, (![A_139, A_140]: (A_139='#skF_4' | ~v2_tex_2(A_139, A_140) | ~m1_subset_1(A_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~v3_tex_2('#skF_4', A_140) | ~l1_pre_topc(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_447])).
% 2.85/1.45  tff(c_470, plain, (![B_10, A_140]: (k1_tarski(B_10)='#skF_4' | ~v2_tex_2(k1_tarski(B_10), A_140) | ~v3_tex_2('#skF_4', A_140) | ~l1_pre_topc(A_140) | u1_struct_0(A_140)='#skF_4' | ~m1_subset_1(B_10, u1_struct_0(A_140)))), inference(resolution, [status(thm)], [c_160, c_451])).
% 2.85/1.45  tff(c_485, plain, (![B_10, A_140]: (~v2_tex_2(k1_tarski(B_10), A_140) | ~v3_tex_2('#skF_4', A_140) | ~l1_pre_topc(A_140) | u1_struct_0(A_140)='#skF_4' | ~m1_subset_1(B_10, u1_struct_0(A_140)))), inference(negUnitSimplification, [status(thm)], [c_101, c_470])).
% 2.85/1.45  tff(c_568, plain, (![A_170]: (~v3_tex_2('#skF_4', A_170) | ~m1_subset_1('#skF_1'(u1_struct_0(A_170)), u1_struct_0(A_170)) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170) | v1_xboole_0(u1_struct_0(A_170)) | u1_struct_0(A_170)='#skF_4')), inference(resolution, [status(thm)], [c_563, c_485])).
% 2.85/1.45  tff(c_573, plain, (![A_171]: (~v3_tex_2('#skF_4', A_171) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171) | v1_xboole_0(u1_struct_0(A_171)) | u1_struct_0(A_171)='#skF_4')), inference(resolution, [status(thm)], [c_111, c_568])).
% 2.85/1.45  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.85/1.45  tff(c_72, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_2])).
% 2.85/1.45  tff(c_582, plain, (![A_172]: (~v3_tex_2('#skF_4', A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172) | u1_struct_0(A_172)='#skF_4')), inference(resolution, [status(thm)], [c_573, c_72])).
% 2.85/1.45  tff(c_588, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_44, c_582])).
% 2.85/1.45  tff(c_592, plain, (v2_struct_0('#skF_3') | u1_struct_0('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_588])).
% 2.85/1.45  tff(c_593, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_592])).
% 2.85/1.45  tff(c_26, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.85/1.45  tff(c_631, plain, (~v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_593, c_26])).
% 2.85/1.45  tff(c_661, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_631])).
% 2.85/1.45  tff(c_662, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_661])).
% 2.85/1.45  tff(c_666, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_662])).
% 2.85/1.45  tff(c_670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_666])).
% 2.85/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.45  
% 2.85/1.45  Inference rules
% 2.85/1.45  ----------------------
% 2.85/1.45  #Ref     : 0
% 2.85/1.45  #Sup     : 124
% 2.85/1.45  #Fact    : 0
% 2.85/1.45  #Define  : 0
% 2.85/1.45  #Split   : 0
% 2.85/1.45  #Chain   : 0
% 2.85/1.45  #Close   : 0
% 2.85/1.45  
% 2.85/1.45  Ordering : KBO
% 2.85/1.45  
% 2.85/1.45  Simplification rules
% 2.85/1.45  ----------------------
% 2.85/1.45  #Subsume      : 3
% 2.85/1.45  #Demod        : 46
% 2.85/1.45  #Tautology    : 32
% 2.85/1.45  #SimpNegUnit  : 8
% 2.85/1.45  #BackRed      : 4
% 2.85/1.45  
% 2.85/1.45  #Partial instantiations: 0
% 2.85/1.45  #Strategies tried      : 1
% 2.85/1.45  
% 2.85/1.45  Timing (in seconds)
% 2.85/1.45  ----------------------
% 2.85/1.46  Preprocessing        : 0.33
% 2.85/1.46  Parsing              : 0.18
% 2.85/1.46  CNF conversion       : 0.02
% 2.85/1.46  Main loop            : 0.36
% 2.85/1.46  Inferencing          : 0.14
% 2.85/1.46  Reduction            : 0.10
% 2.85/1.46  Demodulation         : 0.07
% 2.85/1.46  BG Simplification    : 0.02
% 2.85/1.46  Subsumption          : 0.07
% 2.85/1.46  Abstraction          : 0.02
% 2.85/1.46  MUC search           : 0.00
% 2.85/1.46  Cooper               : 0.00
% 2.85/1.46  Total                : 0.72
% 2.85/1.46  Index Insertion      : 0.00
% 2.85/1.46  Index Deletion       : 0.00
% 2.85/1.46  Index Matching       : 0.00
% 2.85/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
