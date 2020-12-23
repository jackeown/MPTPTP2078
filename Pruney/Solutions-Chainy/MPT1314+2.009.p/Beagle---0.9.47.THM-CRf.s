%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:00 EST 2020

% Result     : Theorem 43.96s
% Output     : CNFRefutation 44.22s
% Verified   : 
% Statistics : Number of formulae       :  255 (55171 expanded)
%              Number of leaves         :   41 (18959 expanded)
%              Depth                    :   35
%              Number of atoms          :  636 (129722 expanded)
%              Number of equality atoms :   76 (24275 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v3_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v3_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

tff(c_62,plain,(
    ~ v3_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_70,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_74,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_109,plain,(
    ! [B_104,A_105] :
      ( l1_pre_topc(B_104)
      | ~ m1_pre_topc(B_104,A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_112,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_109])).

tff(c_115,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_112])).

tff(c_50,plain,(
    ! [A_60] :
      ( l1_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_93,plain,(
    ! [A_100] :
      ( u1_struct_0(A_100) = k2_struct_0(A_100)
      | ~ l1_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_97,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_50,c_93])).

tff(c_119,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_115,c_97])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_120,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_66])).

tff(c_225,plain,(
    ! [A_122,B_123] :
      ( m1_pre_topc(k1_pre_topc(A_122,B_123),A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_227,plain,(
    ! [B_123] :
      ( m1_pre_topc(k1_pre_topc('#skF_7',B_123),'#skF_7')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_7')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_225])).

tff(c_368,plain,(
    ! [B_132] :
      ( m1_pre_topc(k1_pre_topc('#skF_7',B_132),'#skF_7')
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_227])).

tff(c_376,plain,(
    m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_120,c_368])).

tff(c_52,plain,(
    ! [B_63,A_61] :
      ( l1_pre_topc(B_63)
      | ~ m1_pre_topc(B_63,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_381,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_376,c_52])).

tff(c_384,plain,(
    l1_pre_topc(k1_pre_topc('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_381])).

tff(c_134,plain,(
    ! [A_108,B_109] :
      ( v1_pre_topc(k1_pre_topc(A_108,B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_137,plain,(
    ! [B_109] :
      ( v1_pre_topc(k1_pre_topc('#skF_7',B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_7')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_134])).

tff(c_209,plain,(
    ! [B_119] :
      ( v1_pre_topc(k1_pre_topc('#skF_7',B_119))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_137])).

tff(c_217,plain,(
    v1_pre_topc(k1_pre_topc('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_120,c_209])).

tff(c_729,plain,(
    ! [A_147,B_148] :
      ( k2_struct_0(k1_pre_topc(A_147,B_148)) = B_148
      | ~ m1_pre_topc(k1_pre_topc(A_147,B_148),A_147)
      | ~ v1_pre_topc(k1_pre_topc(A_147,B_148))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_739,plain,
    ( k2_struct_0(k1_pre_topc('#skF_7','#skF_8')) = '#skF_8'
    | ~ v1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_376,c_729])).

tff(c_762,plain,(
    k2_struct_0(k1_pre_topc('#skF_7','#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_120,c_119,c_217,c_739])).

tff(c_220,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(k2_struct_0(B_120),k2_struct_0(A_121))
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(B_120)
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_224,plain,(
    ! [B_120,A_121] :
      ( k3_xboole_0(k2_struct_0(B_120),k2_struct_0(A_121)) = k2_struct_0(B_120)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(B_120)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_220,c_2])).

tff(c_783,plain,(
    ! [A_121] :
      ( k3_xboole_0('#skF_8',k2_struct_0(A_121)) = k2_struct_0(k1_pre_topc('#skF_7','#skF_8'))
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_121)
      | ~ l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
      | ~ l1_pre_topc(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_224])).

tff(c_1810,plain,(
    ! [A_182] :
      ( k3_xboole_0('#skF_8',k2_struct_0(A_182)) = '#skF_8'
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_182)
      | ~ l1_pre_topc(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_762,c_783])).

tff(c_1813,plain,
    ( k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8'
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_376,c_1810])).

tff(c_1816,plain,(
    k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_1813])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_172,plain,(
    ! [A_112,B_113,C_114] :
      ( k9_subset_1(A_112,B_113,C_114) = k3_xboole_0(B_113,C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    ! [A_4,B_113] : k9_subset_1(A_4,B_113,A_4) = k3_xboole_0(B_113,A_4) ),
    inference(resolution,[status(thm)],[c_77,c_172])).

tff(c_98,plain,(
    ! [A_101] :
      ( u1_struct_0(A_101) = k2_struct_0(A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_50,c_93])).

tff(c_102,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_98])).

tff(c_1994,plain,(
    ! [B_187,D_188,A_189] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_187),D_188,k2_struct_0(B_187)),B_187)
      | ~ v3_pre_topc(D_188,A_189)
      | ~ m1_subset_1(D_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_187),D_188,k2_struct_0(B_187)),k1_zfmisc_1(u1_struct_0(B_187)))
      | ~ m1_pre_topc(B_187,A_189)
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2016,plain,(
    ! [B_187,D_188] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_187),D_188,k2_struct_0(B_187)),B_187)
      | ~ v3_pre_topc(D_188,'#skF_5')
      | ~ m1_subset_1(D_188,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_187),D_188,k2_struct_0(B_187)),k1_zfmisc_1(u1_struct_0(B_187)))
      | ~ m1_pre_topc(B_187,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1994])).

tff(c_2335,plain,(
    ! [B_199,D_200] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_199),D_200,k2_struct_0(B_199)),B_199)
      | ~ v3_pre_topc(D_200,'#skF_5')
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_199),D_200,k2_struct_0(B_199)),k1_zfmisc_1(u1_struct_0(B_199)))
      | ~ m1_pre_topc(B_199,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2016])).

tff(c_2422,plain,(
    ! [D_200] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_5'),D_200,k2_struct_0('#skF_5')),'#skF_5')
      | ~ v3_pre_topc(D_200,'#skF_5')
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_5'),D_200,k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_2335])).

tff(c_2455,plain,(
    ! [D_200] :
      ( v3_pre_topc(k3_xboole_0(D_200,k2_struct_0('#skF_5')),'#skF_5')
      | ~ v3_pre_topc(D_200,'#skF_5')
      | ~ m1_subset_1(D_200,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k3_xboole_0(D_200,k2_struct_0('#skF_5')),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_102,c_181,c_102,c_2422])).

tff(c_2537,plain,(
    ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2455])).

tff(c_150,plain,(
    ! [A_110] :
      ( v1_pre_topc(k1_pre_topc(A_110,u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_77,c_134])).

tff(c_156,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_150])).

tff(c_160,plain,(
    v1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_156])).

tff(c_238,plain,(
    ! [A_124] :
      ( m1_pre_topc(k1_pre_topc(A_124,u1_struct_0(A_124)),A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_77,c_225])).

tff(c_247,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_238])).

tff(c_252,plain,(
    m1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_247])).

tff(c_743,plain,
    ( k2_struct_0(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) = k2_struct_0('#skF_5')
    | ~ v1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_252,c_729])).

tff(c_768,plain,(
    k2_struct_0(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_77,c_102,c_160,c_743])).

tff(c_276,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_252,c_52])).

tff(c_279,plain,(
    l1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_276])).

tff(c_294,plain,(
    u1_struct_0(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) = k2_struct_0(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_279,c_97])).

tff(c_248,plain,(
    ! [A_124] :
      ( l1_pre_topc(k1_pre_topc(A_124,u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_238,c_52])).

tff(c_433,plain,
    ( l1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')))))
    | ~ l1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_248])).

tff(c_451,plain,(
    l1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_433])).

tff(c_1027,plain,(
    l1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_451])).

tff(c_1029,plain,(
    u1_struct_0(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_294])).

tff(c_237,plain,(
    ! [A_122] :
      ( m1_pre_topc(k1_pre_topc(A_122,u1_struct_0(A_122)),A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(resolution,[status(thm)],[c_77,c_225])).

tff(c_1131,plain,
    ( m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')),k1_pre_topc('#skF_5',k2_struct_0('#skF_5')))
    | ~ l1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_237])).

tff(c_1154,plain,(
    m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')),k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_1131])).

tff(c_149,plain,(
    ! [A_108] :
      ( v1_pre_topc(k1_pre_topc(A_108,u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_77,c_134])).

tff(c_444,plain,
    ( v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')))))
    | ~ l1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_149])).

tff(c_459,plain,(
    v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_444])).

tff(c_1028,plain,(
    v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_459])).

tff(c_14,plain,(
    ! [A_10,B_14] :
      ( k2_struct_0(k1_pre_topc(A_10,B_14)) = B_14
      | ~ m1_pre_topc(k1_pre_topc(A_10,B_14),A_10)
      | ~ v1_pre_topc(k1_pre_topc(A_10,B_14))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1718,plain,
    ( k2_struct_0(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))) = k2_struct_0('#skF_5')
    | ~ v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')))))
    | ~ l1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_1154,c_14])).

tff(c_1724,plain,(
    k2_struct_0(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))) = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_77,c_1029,c_1028,c_1718])).

tff(c_36,plain,(
    ! [B_40,A_18] :
      ( r1_tarski(k2_struct_0(B_40),k2_struct_0(A_18))
      | ~ m1_pre_topc(B_40,A_18)
      | ~ l1_pre_topc(B_40)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1051,plain,(
    ! [B_40] :
      ( r1_tarski(k2_struct_0(B_40),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_40,k1_pre_topc('#skF_5',k2_struct_0('#skF_5')))
      | ~ l1_pre_topc(B_40)
      | ~ l1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_36])).

tff(c_2548,plain,(
    ! [B_207] :
      ( r1_tarski(k2_struct_0(B_207),k2_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_207,k1_pre_topc('#skF_5',k2_struct_0('#skF_5')))
      | ~ l1_pre_topc(B_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_1051])).

tff(c_2557,plain,
    ( r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')),k1_pre_topc('#skF_5',k2_struct_0('#skF_5')))
    | ~ l1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1724,c_2548])).

tff(c_2580,plain,(
    r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1154,c_2557])).

tff(c_463,plain,(
    ! [A_133,B_134] :
      ( m1_subset_1('#skF_2'(A_133,B_134),k1_zfmisc_1(u1_struct_0(B_134)))
      | m1_pre_topc(B_134,A_133)
      | ~ r1_tarski(k2_struct_0(B_134),k2_struct_0(A_133))
      | ~ l1_pre_topc(B_134)
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_487,plain,(
    ! [A_133] :
      ( m1_subset_1('#skF_2'(A_133,'#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | m1_pre_topc('#skF_5',A_133)
      | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0(A_133))
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_463])).

tff(c_501,plain,(
    ! [A_133] :
      ( m1_subset_1('#skF_2'(A_133,'#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | m1_pre_topc('#skF_5',A_133)
      | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0(A_133))
      | ~ l1_pre_topc(A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_487])).

tff(c_48,plain,(
    ! [A_58,B_59] :
      ( v1_pre_topc(k1_pre_topc(A_58,B_59))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3359,plain,(
    ! [B_233,A_234] :
      ( v1_pre_topc(k1_pre_topc(B_233,'#skF_2'(A_234,B_233)))
      | m1_pre_topc(B_233,A_234)
      | ~ r1_tarski(k2_struct_0(B_233),k2_struct_0(A_234))
      | ~ l1_pre_topc(B_233)
      | ~ l1_pre_topc(A_234) ) ),
    inference(resolution,[status(thm)],[c_463,c_48])).

tff(c_3377,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')))
    | m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2580,c_3359])).

tff(c_3436,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')))
    | m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3377])).

tff(c_3437,plain,(
    v1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_3436])).

tff(c_46,plain,(
    ! [A_58,B_59] :
      ( m1_pre_topc(k1_pre_topc(A_58,B_59),A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3756,plain,(
    ! [B_240,A_241] :
      ( m1_pre_topc(k1_pre_topc(B_240,'#skF_2'(A_241,B_240)),B_240)
      | m1_pre_topc(B_240,A_241)
      | ~ r1_tarski(k2_struct_0(B_240),k2_struct_0(A_241))
      | ~ l1_pre_topc(B_240)
      | ~ l1_pre_topc(A_241) ) ),
    inference(resolution,[status(thm)],[c_463,c_46])).

tff(c_3778,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')),'#skF_5')
    | m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2580,c_3756])).

tff(c_3837,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')),'#skF_5')
    | m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3778])).

tff(c_3838,plain,(
    m1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_3837])).

tff(c_3876,plain,
    ( k2_struct_0(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5'))) = '#skF_2'('#skF_5','#skF_5')
    | ~ v1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_3838,c_14])).

tff(c_3882,plain,
    ( k2_struct_0(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5'))) = '#skF_2'('#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_102,c_3437,c_3876])).

tff(c_7260,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_3882])).

tff(c_7263,plain,
    ( m1_pre_topc('#skF_5','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_501,c_7260])).

tff(c_7266,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2580,c_7263])).

tff(c_7268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_7266])).

tff(c_7270,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_3882])).

tff(c_1360,plain,(
    ! [A_163,B_164,C_165] :
      ( m1_subset_1('#skF_1'(A_163,B_164,C_165),k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ r2_hidden(C_165,u1_pre_topc(B_164))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(u1_struct_0(B_164)))
      | ~ m1_pre_topc(B_164,A_163)
      | ~ l1_pre_topc(B_164)
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4270,plain,(
    ! [A_259,B_260,C_261] :
      ( v1_pre_topc(k1_pre_topc(A_259,'#skF_1'(A_259,B_260,C_261)))
      | ~ r2_hidden(C_261,u1_pre_topc(B_260))
      | ~ m1_subset_1(C_261,k1_zfmisc_1(u1_struct_0(B_260)))
      | ~ m1_pre_topc(B_260,A_259)
      | ~ l1_pre_topc(B_260)
      | ~ l1_pre_topc(A_259) ) ),
    inference(resolution,[status(thm)],[c_1360,c_48])).

tff(c_4298,plain,(
    ! [A_259,C_261] :
      ( v1_pre_topc(k1_pre_topc(A_259,'#skF_1'(A_259,'#skF_5',C_261)))
      | ~ r2_hidden(C_261,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5',A_259)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4270])).

tff(c_4323,plain,(
    ! [A_259,C_261] :
      ( v1_pre_topc(k1_pre_topc(A_259,'#skF_1'(A_259,'#skF_5',C_261)))
      | ~ r2_hidden(C_261,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5',A_259)
      | ~ l1_pre_topc(A_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4298])).

tff(c_7300,plain,(
    ! [A_259] :
      ( v1_pre_topc(k1_pre_topc(A_259,'#skF_1'(A_259,'#skF_5','#skF_2'('#skF_5','#skF_5'))))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_259)
      | ~ l1_pre_topc(A_259) ) ),
    inference(resolution,[status(thm)],[c_7270,c_4323])).

tff(c_15652,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7300])).

tff(c_1834,plain,(
    ! [A_184,B_185] :
      ( r2_hidden('#skF_2'(A_184,B_185),u1_pre_topc(B_185))
      | k9_subset_1(u1_struct_0(B_185),'#skF_3'(A_184,B_185),k2_struct_0(B_185)) = '#skF_2'(A_184,B_185)
      | m1_pre_topc(B_185,A_184)
      | ~ r1_tarski(k2_struct_0(B_185),k2_struct_0(A_184))
      | ~ l1_pre_topc(B_185)
      | ~ l1_pre_topc(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1882,plain,(
    ! [A_184] :
      ( r2_hidden('#skF_2'(A_184,'#skF_5'),u1_pre_topc('#skF_5'))
      | k9_subset_1(k2_struct_0('#skF_5'),'#skF_3'(A_184,'#skF_5'),k2_struct_0('#skF_5')) = '#skF_2'(A_184,'#skF_5')
      | m1_pre_topc('#skF_5',A_184)
      | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0(A_184))
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1834])).

tff(c_1911,plain,(
    ! [A_184] :
      ( r2_hidden('#skF_2'(A_184,'#skF_5'),u1_pre_topc('#skF_5'))
      | k3_xboole_0('#skF_3'(A_184,'#skF_5'),k2_struct_0('#skF_5')) = '#skF_2'(A_184,'#skF_5')
      | m1_pre_topc('#skF_5',A_184)
      | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0(A_184))
      | ~ l1_pre_topc(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_181,c_1882])).

tff(c_15675,plain,
    ( k3_xboole_0('#skF_3'('#skF_5','#skF_5'),k2_struct_0('#skF_5')) = '#skF_2'('#skF_5','#skF_5')
    | m1_pre_topc('#skF_5','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1911,c_15652])).

tff(c_15701,plain,
    ( k3_xboole_0('#skF_3'('#skF_5','#skF_5'),k2_struct_0('#skF_5')) = '#skF_2'('#skF_5','#skF_5')
    | m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2580,c_15675])).

tff(c_15702,plain,(
    k3_xboole_0('#skF_3'('#skF_5','#skF_5'),k2_struct_0('#skF_5')) = '#skF_2'('#skF_5','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_15701])).

tff(c_1463,plain,(
    ! [A_170,B_171] :
      ( r2_hidden('#skF_2'(A_170,B_171),u1_pre_topc(B_171))
      | m1_subset_1('#skF_3'(A_170,B_171),k1_zfmisc_1(u1_struct_0(A_170)))
      | m1_pre_topc(B_171,A_170)
      | ~ r1_tarski(k2_struct_0(B_171),k2_struct_0(A_170))
      | ~ l1_pre_topc(B_171)
      | ~ l1_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1495,plain,(
    ! [A_170,B_171] :
      ( m1_pre_topc(k1_pre_topc(A_170,'#skF_3'(A_170,B_171)),A_170)
      | r2_hidden('#skF_2'(A_170,B_171),u1_pre_topc(B_171))
      | m1_pre_topc(B_171,A_170)
      | ~ r1_tarski(k2_struct_0(B_171),k2_struct_0(A_170))
      | ~ l1_pre_topc(B_171)
      | ~ l1_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_1463,c_46])).

tff(c_15669,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')),'#skF_5')
    | m1_pre_topc('#skF_5','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1495,c_15652])).

tff(c_15693,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')),'#skF_5')
    | m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2580,c_15669])).

tff(c_15694,plain,(
    m1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_15693])).

tff(c_4669,plain,(
    ! [A_283,B_284] :
      ( m1_pre_topc(k1_pre_topc(A_283,'#skF_3'(A_283,B_284)),A_283)
      | r2_hidden('#skF_2'(A_283,B_284),u1_pre_topc(B_284))
      | m1_pre_topc(B_284,A_283)
      | ~ r1_tarski(k2_struct_0(B_284),k2_struct_0(A_283))
      | ~ l1_pre_topc(B_284)
      | ~ l1_pre_topc(A_283) ) ),
    inference(resolution,[status(thm)],[c_1463,c_46])).

tff(c_4718,plain,(
    ! [A_283,B_284] :
      ( l1_pre_topc(k1_pre_topc(A_283,'#skF_3'(A_283,B_284)))
      | r2_hidden('#skF_2'(A_283,B_284),u1_pre_topc(B_284))
      | m1_pre_topc(B_284,A_283)
      | ~ r1_tarski(k2_struct_0(B_284),k2_struct_0(A_283))
      | ~ l1_pre_topc(B_284)
      | ~ l1_pre_topc(A_283) ) ),
    inference(resolution,[status(thm)],[c_4669,c_52])).

tff(c_15655,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')))
    | m1_pre_topc('#skF_5','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_4718,c_15652])).

tff(c_15681,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')))
    | m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2580,c_15655])).

tff(c_15682,plain,(
    l1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_15681])).

tff(c_1493,plain,(
    ! [B_171] :
      ( r2_hidden('#skF_2'('#skF_5',B_171),u1_pre_topc(B_171))
      | m1_subset_1('#skF_3'('#skF_5',B_171),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | m1_pre_topc(B_171,'#skF_5')
      | ~ r1_tarski(k2_struct_0(B_171),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc(B_171)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1463])).

tff(c_1509,plain,(
    ! [B_171] :
      ( r2_hidden('#skF_2'('#skF_5',B_171),u1_pre_topc(B_171))
      | m1_subset_1('#skF_3'('#skF_5',B_171),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | m1_pre_topc(B_171,'#skF_5')
      | ~ r1_tarski(k2_struct_0(B_171),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc(B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1493])).

tff(c_1497,plain,(
    ! [A_170,B_171] :
      ( v1_pre_topc(k1_pre_topc(A_170,'#skF_3'(A_170,B_171)))
      | r2_hidden('#skF_2'(A_170,B_171),u1_pre_topc(B_171))
      | m1_pre_topc(B_171,A_170)
      | ~ r1_tarski(k2_struct_0(B_171),k2_struct_0(A_170))
      | ~ l1_pre_topc(B_171)
      | ~ l1_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_1463,c_48])).

tff(c_15672,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')))
    | m1_pre_topc('#skF_5','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1497,c_15652])).

tff(c_15697,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')))
    | m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2580,c_15672])).

tff(c_15698,plain,(
    v1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_15697])).

tff(c_15708,plain,
    ( k2_struct_0(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5'))) = '#skF_3'('#skF_5','#skF_5')
    | ~ v1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')))
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_15694,c_14])).

tff(c_15714,plain,
    ( k2_struct_0(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5'))) = '#skF_3'('#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_102,c_15698,c_15708])).

tff(c_16336,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_15714])).

tff(c_16339,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5'))
    | m1_pre_topc('#skF_5','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1509,c_16336])).

tff(c_16342,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5'))
    | m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2580,c_16339])).

tff(c_16344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_15652,c_16342])).

tff(c_16345,plain,(
    k2_struct_0(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5'))) = '#skF_3'('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_15714])).

tff(c_16506,plain,(
    ! [A_121] :
      ( k3_xboole_0('#skF_3'('#skF_5','#skF_5'),k2_struct_0(A_121)) = k2_struct_0(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')))
      | ~ m1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')),A_121)
      | ~ l1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')))
      | ~ l1_pre_topc(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16345,c_224])).

tff(c_18262,plain,(
    ! [A_658] :
      ( k3_xboole_0('#skF_3'('#skF_5','#skF_5'),k2_struct_0(A_658)) = '#skF_3'('#skF_5','#skF_5')
      | ~ m1_pre_topc(k1_pre_topc('#skF_5','#skF_3'('#skF_5','#skF_5')),A_658)
      | ~ l1_pre_topc(A_658) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15682,c_16345,c_16506])).

tff(c_18265,plain,
    ( k3_xboole_0('#skF_3'('#skF_5','#skF_5'),k2_struct_0('#skF_5')) = '#skF_3'('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_15694,c_18262])).

tff(c_18270,plain,(
    '#skF_3'('#skF_5','#skF_5') = '#skF_2'('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_15702,c_18265])).

tff(c_30,plain,(
    ! [A_18,B_40] :
      ( r2_hidden('#skF_2'(A_18,B_40),u1_pre_topc(B_40))
      | r2_hidden('#skF_3'(A_18,B_40),u1_pre_topc(A_18))
      | m1_pre_topc(B_40,A_18)
      | ~ r1_tarski(k2_struct_0(B_40),k2_struct_0(A_18))
      | ~ l1_pre_topc(B_40)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16346,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_15714])).

tff(c_16400,plain,(
    ! [A_259] :
      ( v1_pre_topc(k1_pre_topc(A_259,'#skF_1'(A_259,'#skF_5','#skF_3'('#skF_5','#skF_5'))))
      | ~ r2_hidden('#skF_3'('#skF_5','#skF_5'),u1_pre_topc('#skF_5'))
      | ~ m1_pre_topc('#skF_5',A_259)
      | ~ l1_pre_topc(A_259) ) ),
    inference(resolution,[status(thm)],[c_16346,c_4323])).

tff(c_18271,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_16400])).

tff(c_18274,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5'))
    | m1_pre_topc('#skF_5','#skF_5')
    | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_18271])).

tff(c_18277,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5'))
    | m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2580,c_18274])).

tff(c_18279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_15652,c_18277])).

tff(c_18281,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_16400])).

tff(c_18288,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18270,c_18281])).

tff(c_18324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15652,c_18288])).

tff(c_18326,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7300])).

tff(c_3879,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_3838,c_52])).

tff(c_3885,plain,(
    l1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3879])).

tff(c_7269,plain,(
    k2_struct_0(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5'))) = '#skF_2'('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3882])).

tff(c_7383,plain,(
    ! [A_121] :
      ( k3_xboole_0('#skF_2'('#skF_5','#skF_5'),k2_struct_0(A_121)) = k2_struct_0(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')))
      | ~ m1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')),A_121)
      | ~ l1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')))
      | ~ l1_pre_topc(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7269,c_224])).

tff(c_13202,plain,(
    ! [A_546] :
      ( k3_xboole_0('#skF_2'('#skF_5','#skF_5'),k2_struct_0(A_546)) = '#skF_2'('#skF_5','#skF_5')
      | ~ m1_pre_topc(k1_pre_topc('#skF_5','#skF_2'('#skF_5','#skF_5')),A_546)
      | ~ l1_pre_topc(A_546) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3885,c_7269,c_7383])).

tff(c_13209,plain,
    ( k3_xboole_0('#skF_2'('#skF_5','#skF_5'),k2_struct_0('#skF_5')) = '#skF_2'('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_3838,c_13202])).

tff(c_13216,plain,(
    k3_xboole_0('#skF_2'('#skF_5','#skF_5'),k2_struct_0('#skF_5')) = '#skF_2'('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_13209])).

tff(c_2460,plain,(
    ! [B_201,D_202,A_203] :
      ( k9_subset_1(u1_struct_0(B_201),D_202,k2_struct_0(B_201)) != '#skF_2'(A_203,B_201)
      | ~ r2_hidden(D_202,u1_pre_topc(A_203))
      | ~ m1_subset_1(D_202,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ r2_hidden('#skF_2'(A_203,B_201),u1_pre_topc(B_201))
      | m1_pre_topc(B_201,A_203)
      | ~ r1_tarski(k2_struct_0(B_201),k2_struct_0(A_203))
      | ~ l1_pre_topc(B_201)
      | ~ l1_pre_topc(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2500,plain,(
    ! [D_202,A_203] :
      ( k9_subset_1(k2_struct_0('#skF_5'),D_202,k2_struct_0('#skF_5')) != '#skF_2'(A_203,'#skF_5')
      | ~ r2_hidden(D_202,u1_pre_topc(A_203))
      | ~ m1_subset_1(D_202,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ r2_hidden('#skF_2'(A_203,'#skF_5'),u1_pre_topc('#skF_5'))
      | m1_pre_topc('#skF_5',A_203)
      | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0(A_203))
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_2460])).

tff(c_3049,plain,(
    ! [D_230,A_231] :
      ( k3_xboole_0(D_230,k2_struct_0('#skF_5')) != '#skF_2'(A_231,'#skF_5')
      | ~ r2_hidden(D_230,u1_pre_topc(A_231))
      | ~ m1_subset_1(D_230,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ r2_hidden('#skF_2'(A_231,'#skF_5'),u1_pre_topc('#skF_5'))
      | m1_pre_topc('#skF_5',A_231)
      | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0(A_231))
      | ~ l1_pre_topc(A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_181,c_2500])).

tff(c_3075,plain,(
    ! [D_230] :
      ( k3_xboole_0(D_230,k2_struct_0('#skF_5')) != '#skF_2'('#skF_5','#skF_5')
      | ~ r2_hidden(D_230,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(D_230,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5'))
      | m1_pre_topc('#skF_5','#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_3049])).

tff(c_3098,plain,(
    ! [D_230] :
      ( k3_xboole_0(D_230,k2_struct_0('#skF_5')) != '#skF_2'('#skF_5','#skF_5')
      | ~ r2_hidden(D_230,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(D_230,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5'))
      | m1_pre_topc('#skF_5','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2580,c_3075])).

tff(c_3099,plain,(
    ! [D_230] :
      ( k3_xboole_0(D_230,k2_struct_0('#skF_5')) != '#skF_2'('#skF_5','#skF_5')
      | ~ r2_hidden(D_230,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(D_230,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2537,c_3098])).

tff(c_22546,plain,(
    ! [D_734] :
      ( k3_xboole_0(D_734,k2_struct_0('#skF_5')) != '#skF_2'('#skF_5','#skF_5')
      | ~ r2_hidden(D_734,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(D_734,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18326,c_3099])).

tff(c_22549,plain,
    ( k3_xboole_0('#skF_2'('#skF_5','#skF_5'),k2_struct_0('#skF_5')) != '#skF_2'('#skF_5','#skF_5')
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(resolution,[status(thm)],[c_7270,c_22546])).

tff(c_22572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18326,c_13216,c_22549])).

tff(c_22574,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2455])).

tff(c_64,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_76,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_72])).

tff(c_103,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_76])).

tff(c_68,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_75,plain,(
    v3_pre_topc('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68])).

tff(c_634,plain,(
    ! [A_139,B_140,C_141] :
      ( m1_subset_1('#skF_4'(A_139,B_140,C_141),k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ v3_pre_topc(C_141,B_140)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(B_140)))
      | ~ m1_pre_topc(B_140,A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_664,plain,(
    ! [B_140,C_141] :
      ( m1_subset_1('#skF_4'('#skF_5',B_140,C_141),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ v3_pre_topc(C_141,B_140)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(B_140)))
      | ~ m1_pre_topc(B_140,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_634])).

tff(c_1221,plain,(
    ! [B_156,C_157] :
      ( m1_subset_1('#skF_4'('#skF_5',B_156,C_157),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ v3_pre_topc(C_157,B_156)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(u1_struct_0(B_156)))
      | ~ m1_pre_topc(B_156,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_664])).

tff(c_229,plain,(
    ! [B_123] :
      ( m1_pre_topc(k1_pre_topc('#skF_5',B_123),'#skF_5')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_225])).

tff(c_236,plain,(
    ! [B_123] :
      ( m1_pre_topc(k1_pre_topc('#skF_5',B_123),'#skF_5')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_229])).

tff(c_47993,plain,(
    ! [B_1407,C_1408] :
      ( m1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5',B_1407,C_1408)),'#skF_5')
      | ~ v3_pre_topc(C_1408,B_1407)
      | ~ m1_subset_1(C_1408,k1_zfmisc_1(u1_struct_0(B_1407)))
      | ~ m1_pre_topc(B_1407,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1221,c_236])).

tff(c_48050,plain,(
    ! [C_1408] :
      ( m1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5',C_1408)),'#skF_5')
      | ~ v3_pre_topc(C_1408,'#skF_5')
      | ~ m1_subset_1(C_1408,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_47993])).

tff(c_48086,plain,(
    ! [C_1410] :
      ( m1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5',C_1410)),'#skF_5')
      | ~ v3_pre_topc(C_1410,'#skF_5')
      | ~ m1_subset_1(C_1410,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22574,c_48050])).

tff(c_48101,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8')),'#skF_5')
    | ~ v3_pre_topc('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_48086])).

tff(c_48112,plain,(
    m1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_48101])).

tff(c_48125,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48112,c_52])).

tff(c_48131,plain,(
    l1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_48125])).

tff(c_680,plain,(
    ! [B_140,C_141] :
      ( m1_subset_1('#skF_4'('#skF_5',B_140,C_141),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ v3_pre_topc(C_141,B_140)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(B_140)))
      | ~ m1_pre_topc(B_140,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_664])).

tff(c_140,plain,(
    ! [B_109] :
      ( v1_pre_topc(k1_pre_topc('#skF_5',B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_134])).

tff(c_148,plain,(
    ! [B_109] :
      ( v1_pre_topc(k1_pre_topc('#skF_5',B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_140])).

tff(c_29589,plain,(
    ! [B_966,C_967] :
      ( v1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5',B_966,C_967)))
      | ~ v3_pre_topc(C_967,B_966)
      | ~ m1_subset_1(C_967,k1_zfmisc_1(u1_struct_0(B_966)))
      | ~ m1_pre_topc(B_966,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1221,c_148])).

tff(c_29646,plain,(
    ! [C_967] :
      ( v1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5',C_967)))
      | ~ v3_pre_topc(C_967,'#skF_5')
      | ~ m1_subset_1(C_967,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_29589])).

tff(c_29678,plain,(
    ! [C_969] :
      ( v1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5',C_969)))
      | ~ v3_pre_topc(C_969,'#skF_5')
      | ~ m1_subset_1(C_969,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22574,c_29646])).

tff(c_29693,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8')))
    | ~ v3_pre_topc('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_29678])).

tff(c_29704,plain,(
    v1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_29693])).

tff(c_48122,plain,
    ( k2_struct_0(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8'))) = '#skF_4'('#skF_5','#skF_5','#skF_8')
    | ~ v1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8')))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_5','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48112,c_14])).

tff(c_48128,plain,
    ( k2_struct_0(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8'))) = '#skF_4'('#skF_5','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_5','#skF_8'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_102,c_29704,c_48122])).

tff(c_49943,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_5','#skF_8'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_48128])).

tff(c_49946,plain,
    ( ~ v3_pre_topc('#skF_8','#skF_5')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_680,c_49943])).

tff(c_49950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22574,c_103,c_102,c_75,c_49946])).

tff(c_49951,plain,(
    k2_struct_0(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8'))) = '#skF_4'('#skF_5','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_48128])).

tff(c_50102,plain,(
    ! [A_121] :
      ( k3_xboole_0('#skF_4'('#skF_5','#skF_5','#skF_8'),k2_struct_0(A_121)) = k2_struct_0(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8')))
      | ~ m1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8')),A_121)
      | ~ l1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8')))
      | ~ l1_pre_topc(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49951,c_224])).

tff(c_75513,plain,(
    ! [A_1872] :
      ( k3_xboole_0('#skF_4'('#skF_5','#skF_5','#skF_8'),k2_struct_0(A_1872)) = '#skF_4'('#skF_5','#skF_5','#skF_8')
      | ~ m1_pre_topc(k1_pre_topc('#skF_5','#skF_4'('#skF_5','#skF_5','#skF_8')),A_1872)
      | ~ l1_pre_topc(A_1872) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48131,c_49951,c_50102])).

tff(c_75516,plain,
    ( k3_xboole_0('#skF_4'('#skF_5','#skF_5','#skF_8'),k2_struct_0('#skF_5')) = '#skF_4'('#skF_5','#skF_5','#skF_8')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48112,c_75513])).

tff(c_75523,plain,(
    k3_xboole_0('#skF_4'('#skF_5','#skF_5','#skF_8'),k2_struct_0('#skF_5')) = '#skF_4'('#skF_5','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_75516])).

tff(c_959,plain,(
    ! [B_149,A_150,C_151] :
      ( k9_subset_1(u1_struct_0(B_149),'#skF_4'(A_150,B_149,C_151),k2_struct_0(B_149)) = C_151
      | ~ v3_pre_topc(C_151,B_149)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0(B_149)))
      | ~ m1_pre_topc(B_149,A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_992,plain,(
    ! [A_150,C_151] :
      ( k9_subset_1(k2_struct_0('#skF_5'),'#skF_4'(A_150,'#skF_5',C_151),k2_struct_0('#skF_5')) = C_151
      | ~ v3_pre_topc(C_151,'#skF_5')
      | ~ m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5',A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_959])).

tff(c_1293,plain,(
    ! [A_160,C_161] :
      ( k3_xboole_0('#skF_4'(A_160,'#skF_5',C_161),k2_struct_0('#skF_5')) = C_161
      | ~ v3_pre_topc(C_161,'#skF_5')
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5',A_160)
      | ~ l1_pre_topc(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_181,c_992])).

tff(c_1299,plain,(
    ! [A_160] :
      ( k3_xboole_0('#skF_4'(A_160,'#skF_5','#skF_8'),k2_struct_0('#skF_5')) = '#skF_8'
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_160)
      | ~ l1_pre_topc(A_160) ) ),
    inference(resolution,[status(thm)],[c_103,c_1293])).

tff(c_1307,plain,(
    ! [A_160] :
      ( k3_xboole_0('#skF_4'(A_160,'#skF_5','#skF_8'),k2_struct_0('#skF_5')) = '#skF_8'
      | ~ m1_pre_topc('#skF_5',A_160)
      | ~ l1_pre_topc(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1299])).

tff(c_75536,plain,
    ( '#skF_4'('#skF_5','#skF_5','#skF_8') = '#skF_8'
    | ~ m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_75523,c_1307])).

tff(c_75548,plain,(
    '#skF_4'('#skF_5','#skF_5','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22574,c_75536])).

tff(c_60,plain,(
    ! [A_64,B_76,C_82] :
      ( m1_subset_1('#skF_4'(A_64,B_76,C_82),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ v3_pre_topc(C_82,B_76)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(u1_struct_0(B_76)))
      | ~ m1_pre_topc(B_76,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2030,plain,(
    ! [B_187,A_64,B_76,C_82] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_187),'#skF_4'(A_64,B_76,C_82),k2_struct_0(B_187)),B_187)
      | ~ v3_pre_topc('#skF_4'(A_64,B_76,C_82),A_64)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_187),'#skF_4'(A_64,B_76,C_82),k2_struct_0(B_187)),k1_zfmisc_1(u1_struct_0(B_187)))
      | ~ m1_pre_topc(B_187,A_64)
      | ~ v3_pre_topc(C_82,B_76)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(u1_struct_0(B_76)))
      | ~ m1_pre_topc(B_76,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_60,c_1994])).

tff(c_75680,plain,(
    ! [B_187] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_187),'#skF_4'('#skF_5','#skF_5','#skF_8'),k2_struct_0(B_187)),B_187)
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_187),'#skF_4'('#skF_5','#skF_5','#skF_8'),k2_struct_0(B_187)),k1_zfmisc_1(u1_struct_0(B_187)))
      | ~ m1_pre_topc(B_187,'#skF_5')
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75548,c_2030])).

tff(c_77707,plain,(
    ! [B_1903] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_1903),'#skF_8',k2_struct_0(B_1903)),B_1903)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_1903),'#skF_8',k2_struct_0(B_1903)),k1_zfmisc_1(u1_struct_0(B_1903)))
      | ~ m1_pre_topc(B_1903,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22574,c_103,c_102,c_75,c_75548,c_75,c_75548,c_75680])).

tff(c_77905,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',k2_struct_0('#skF_7')),'#skF_7')
    | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_7'),'#skF_8',k2_struct_0('#skF_7')),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_pre_topc('#skF_7','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_77707])).

tff(c_78007,plain,(
    v3_pre_topc('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_120,c_119,c_1816,c_181,c_1816,c_181,c_119,c_77905])).

tff(c_78009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_78007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.96/28.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.96/28.20  
% 43.96/28.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.96/28.20  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 43.96/28.20  
% 43.96/28.20  %Foreground sorts:
% 43.96/28.20  
% 43.96/28.20  
% 43.96/28.20  %Background operators:
% 43.96/28.20  
% 43.96/28.20  
% 43.96/28.20  %Foreground operators:
% 43.96/28.20  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 43.96/28.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 43.96/28.20  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 43.96/28.20  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 43.96/28.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.96/28.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 43.96/28.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 43.96/28.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 43.96/28.20  tff('#skF_7', type, '#skF_7': $i).
% 43.96/28.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 43.96/28.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 43.96/28.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 43.96/28.20  tff('#skF_5', type, '#skF_5': $i).
% 43.96/28.20  tff('#skF_6', type, '#skF_6': $i).
% 43.96/28.20  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 43.96/28.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 43.96/28.20  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 43.96/28.20  tff('#skF_8', type, '#skF_8': $i).
% 43.96/28.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.96/28.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.96/28.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 43.96/28.20  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 43.96/28.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 43.96/28.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 43.96/28.20  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 43.96/28.20  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 43.96/28.20  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 43.96/28.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 43.96/28.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 43.96/28.20  
% 44.22/28.23  tff(f_132, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 44.22/28.23  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 44.22/28.23  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 44.22/28.23  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 44.22/28.23  tff(f_86, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 44.22/28.23  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 44.22/28.23  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 44.22/28.23  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 44.22/28.23  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 44.22/28.23  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 44.22/28.23  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 44.22/28.23  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 44.22/28.23  tff(c_62, plain, (~v3_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.22/28.23  tff(c_70, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.22/28.23  tff(c_74, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.22/28.23  tff(c_109, plain, (![B_104, A_105]: (l1_pre_topc(B_104) | ~m1_pre_topc(B_104, A_105) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_97])).
% 44.22/28.23  tff(c_112, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_70, c_109])).
% 44.22/28.23  tff(c_115, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_112])).
% 44.22/28.23  tff(c_50, plain, (![A_60]: (l1_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_90])).
% 44.22/28.23  tff(c_93, plain, (![A_100]: (u1_struct_0(A_100)=k2_struct_0(A_100) | ~l1_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_57])).
% 44.22/28.23  tff(c_97, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_50, c_93])).
% 44.22/28.23  tff(c_119, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_115, c_97])).
% 44.22/28.23  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.22/28.23  tff(c_120, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_66])).
% 44.22/28.23  tff(c_225, plain, (![A_122, B_123]: (m1_pre_topc(k1_pre_topc(A_122, B_123), A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_86])).
% 44.22/28.23  tff(c_227, plain, (![B_123]: (m1_pre_topc(k1_pre_topc('#skF_7', B_123), '#skF_7') | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_225])).
% 44.22/28.23  tff(c_368, plain, (![B_132]: (m1_pre_topc(k1_pre_topc('#skF_7', B_132), '#skF_7') | ~m1_subset_1(B_132, k1_zfmisc_1(k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_227])).
% 44.22/28.23  tff(c_376, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_120, c_368])).
% 44.22/28.23  tff(c_52, plain, (![B_63, A_61]: (l1_pre_topc(B_63) | ~m1_pre_topc(B_63, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_97])).
% 44.22/28.23  tff(c_381, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_376, c_52])).
% 44.22/28.23  tff(c_384, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_381])).
% 44.22/28.23  tff(c_134, plain, (![A_108, B_109]: (v1_pre_topc(k1_pre_topc(A_108, B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_86])).
% 44.22/28.23  tff(c_137, plain, (![B_109]: (v1_pre_topc(k1_pre_topc('#skF_7', B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_134])).
% 44.22/28.23  tff(c_209, plain, (![B_119]: (v1_pre_topc(k1_pre_topc('#skF_7', B_119)) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_137])).
% 44.22/28.23  tff(c_217, plain, (v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_120, c_209])).
% 44.22/28.23  tff(c_729, plain, (![A_147, B_148]: (k2_struct_0(k1_pre_topc(A_147, B_148))=B_148 | ~m1_pre_topc(k1_pre_topc(A_147, B_148), A_147) | ~v1_pre_topc(k1_pre_topc(A_147, B_148)) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_53])).
% 44.22/28.23  tff(c_739, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))='#skF_8' | ~v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_376, c_729])).
% 44.22/28.23  tff(c_762, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_120, c_119, c_217, c_739])).
% 44.22/28.23  tff(c_220, plain, (![B_120, A_121]: (r1_tarski(k2_struct_0(B_120), k2_struct_0(A_121)) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(B_120) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_78])).
% 44.22/28.23  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 44.22/28.23  tff(c_224, plain, (![B_120, A_121]: (k3_xboole_0(k2_struct_0(B_120), k2_struct_0(A_121))=k2_struct_0(B_120) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(B_120) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_220, c_2])).
% 44.22/28.23  tff(c_783, plain, (![A_121]: (k3_xboole_0('#skF_8', k2_struct_0(A_121))=k2_struct_0(k1_pre_topc('#skF_7', '#skF_8')) | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_121) | ~l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc(A_121))), inference(superposition, [status(thm), theory('equality')], [c_762, c_224])).
% 44.22/28.23  tff(c_1810, plain, (![A_182]: (k3_xboole_0('#skF_8', k2_struct_0(A_182))='#skF_8' | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_182) | ~l1_pre_topc(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_384, c_762, c_783])).
% 44.22/28.23  tff(c_1813, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8' | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_376, c_1810])).
% 44.22/28.23  tff(c_1816, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_1813])).
% 44.22/28.23  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 44.22/28.23  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 44.22/28.23  tff(c_77, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 44.22/28.23  tff(c_172, plain, (![A_112, B_113, C_114]: (k9_subset_1(A_112, B_113, C_114)=k3_xboole_0(B_113, C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 44.22/28.23  tff(c_181, plain, (![A_4, B_113]: (k9_subset_1(A_4, B_113, A_4)=k3_xboole_0(B_113, A_4))), inference(resolution, [status(thm)], [c_77, c_172])).
% 44.22/28.23  tff(c_98, plain, (![A_101]: (u1_struct_0(A_101)=k2_struct_0(A_101) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_50, c_93])).
% 44.22/28.23  tff(c_102, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_98])).
% 44.22/28.23  tff(c_1994, plain, (![B_187, D_188, A_189]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_187), D_188, k2_struct_0(B_187)), B_187) | ~v3_pre_topc(D_188, A_189) | ~m1_subset_1(D_188, k1_zfmisc_1(u1_struct_0(A_189))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_187), D_188, k2_struct_0(B_187)), k1_zfmisc_1(u1_struct_0(B_187))) | ~m1_pre_topc(B_187, A_189) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_114])).
% 44.22/28.23  tff(c_2016, plain, (![B_187, D_188]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_187), D_188, k2_struct_0(B_187)), B_187) | ~v3_pre_topc(D_188, '#skF_5') | ~m1_subset_1(D_188, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_187), D_188, k2_struct_0(B_187)), k1_zfmisc_1(u1_struct_0(B_187))) | ~m1_pre_topc(B_187, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1994])).
% 44.22/28.23  tff(c_2335, plain, (![B_199, D_200]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_199), D_200, k2_struct_0(B_199)), B_199) | ~v3_pre_topc(D_200, '#skF_5') | ~m1_subset_1(D_200, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_199), D_200, k2_struct_0(B_199)), k1_zfmisc_1(u1_struct_0(B_199))) | ~m1_pre_topc(B_199, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2016])).
% 44.22/28.23  tff(c_2422, plain, (![D_200]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_5'), D_200, k2_struct_0('#skF_5')), '#skF_5') | ~v3_pre_topc(D_200, '#skF_5') | ~m1_subset_1(D_200, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_5'), D_200, k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_2335])).
% 44.22/28.23  tff(c_2455, plain, (![D_200]: (v3_pre_topc(k3_xboole_0(D_200, k2_struct_0('#skF_5')), '#skF_5') | ~v3_pre_topc(D_200, '#skF_5') | ~m1_subset_1(D_200, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(k3_xboole_0(D_200, k2_struct_0('#skF_5')), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_102, c_181, c_102, c_2422])).
% 44.22/28.23  tff(c_2537, plain, (~m1_pre_topc('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_2455])).
% 44.22/28.23  tff(c_150, plain, (![A_110]: (v1_pre_topc(k1_pre_topc(A_110, u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_77, c_134])).
% 44.22/28.23  tff(c_156, plain, (v1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_102, c_150])).
% 44.22/28.23  tff(c_160, plain, (v1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_156])).
% 44.22/28.23  tff(c_238, plain, (![A_124]: (m1_pre_topc(k1_pre_topc(A_124, u1_struct_0(A_124)), A_124) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_77, c_225])).
% 44.22/28.23  tff(c_247, plain, (m1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_102, c_238])).
% 44.22/28.23  tff(c_252, plain, (m1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_247])).
% 44.22/28.23  tff(c_743, plain, (k2_struct_0(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))=k2_struct_0('#skF_5') | ~v1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_252, c_729])).
% 44.22/28.23  tff(c_768, plain, (k2_struct_0(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_77, c_102, c_160, c_743])).
% 44.22/28.23  tff(c_276, plain, (l1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_252, c_52])).
% 44.22/28.23  tff(c_279, plain, (l1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_276])).
% 44.22/28.23  tff(c_294, plain, (u1_struct_0(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))=k2_struct_0(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_279, c_97])).
% 44.22/28.23  tff(c_248, plain, (![A_124]: (l1_pre_topc(k1_pre_topc(A_124, u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_238, c_52])).
% 44.22/28.23  tff(c_433, plain, (l1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0(k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))))) | ~l1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_294, c_248])).
% 44.22/28.23  tff(c_451, plain, (l1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_433])).
% 44.22/28.23  tff(c_1027, plain, (l1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_768, c_451])).
% 44.22/28.23  tff(c_1029, plain, (u1_struct_0(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_768, c_294])).
% 44.22/28.23  tff(c_237, plain, (![A_122]: (m1_pre_topc(k1_pre_topc(A_122, u1_struct_0(A_122)), A_122) | ~l1_pre_topc(A_122))), inference(resolution, [status(thm)], [c_77, c_225])).
% 44.22/28.23  tff(c_1131, plain, (m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')), k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))) | ~l1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1029, c_237])).
% 44.22/28.23  tff(c_1154, plain, (m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')), k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_1131])).
% 44.22/28.23  tff(c_149, plain, (![A_108]: (v1_pre_topc(k1_pre_topc(A_108, u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_77, c_134])).
% 44.22/28.23  tff(c_444, plain, (v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0(k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))))) | ~l1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_294, c_149])).
% 44.22/28.23  tff(c_459, plain, (v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_444])).
% 44.22/28.23  tff(c_1028, plain, (v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_768, c_459])).
% 44.22/28.23  tff(c_14, plain, (![A_10, B_14]: (k2_struct_0(k1_pre_topc(A_10, B_14))=B_14 | ~m1_pre_topc(k1_pre_topc(A_10, B_14), A_10) | ~v1_pre_topc(k1_pre_topc(A_10, B_14)) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 44.22/28.23  tff(c_1718, plain, (k2_struct_0(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')))=k2_struct_0('#skF_5') | ~v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))))) | ~l1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_1154, c_14])).
% 44.22/28.23  tff(c_1724, plain, (k2_struct_0(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')))=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_77, c_1029, c_1028, c_1718])).
% 44.22/28.23  tff(c_36, plain, (![B_40, A_18]: (r1_tarski(k2_struct_0(B_40), k2_struct_0(A_18)) | ~m1_pre_topc(B_40, A_18) | ~l1_pre_topc(B_40) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 44.22/28.23  tff(c_1051, plain, (![B_40]: (r1_tarski(k2_struct_0(B_40), k2_struct_0('#skF_5')) | ~m1_pre_topc(B_40, k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))) | ~l1_pre_topc(B_40) | ~l1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_768, c_36])).
% 44.22/28.23  tff(c_2548, plain, (![B_207]: (r1_tarski(k2_struct_0(B_207), k2_struct_0('#skF_5')) | ~m1_pre_topc(B_207, k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))) | ~l1_pre_topc(B_207))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_1051])).
% 44.22/28.23  tff(c_2557, plain, (r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')), k1_pre_topc('#skF_5', k2_struct_0('#skF_5'))) | ~l1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1724, c_2548])).
% 44.22/28.23  tff(c_2580, plain, (r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1154, c_2557])).
% 44.22/28.23  tff(c_463, plain, (![A_133, B_134]: (m1_subset_1('#skF_2'(A_133, B_134), k1_zfmisc_1(u1_struct_0(B_134))) | m1_pre_topc(B_134, A_133) | ~r1_tarski(k2_struct_0(B_134), k2_struct_0(A_133)) | ~l1_pre_topc(B_134) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_78])).
% 44.22/28.23  tff(c_487, plain, (![A_133]: (m1_subset_1('#skF_2'(A_133, '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | m1_pre_topc('#skF_5', A_133) | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0(A_133)) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_133))), inference(superposition, [status(thm), theory('equality')], [c_102, c_463])).
% 44.22/28.23  tff(c_501, plain, (![A_133]: (m1_subset_1('#skF_2'(A_133, '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | m1_pre_topc('#skF_5', A_133) | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0(A_133)) | ~l1_pre_topc(A_133))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_487])).
% 44.22/28.23  tff(c_48, plain, (![A_58, B_59]: (v1_pre_topc(k1_pre_topc(A_58, B_59)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_86])).
% 44.22/28.23  tff(c_3359, plain, (![B_233, A_234]: (v1_pre_topc(k1_pre_topc(B_233, '#skF_2'(A_234, B_233))) | m1_pre_topc(B_233, A_234) | ~r1_tarski(k2_struct_0(B_233), k2_struct_0(A_234)) | ~l1_pre_topc(B_233) | ~l1_pre_topc(A_234))), inference(resolution, [status(thm)], [c_463, c_48])).
% 44.22/28.23  tff(c_3377, plain, (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5'))) | m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2580, c_3359])).
% 44.22/28.23  tff(c_3436, plain, (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5'))) | m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3377])).
% 44.22/28.23  tff(c_3437, plain, (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2537, c_3436])).
% 44.22/28.23  tff(c_46, plain, (![A_58, B_59]: (m1_pre_topc(k1_pre_topc(A_58, B_59), A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_86])).
% 44.22/28.23  tff(c_3756, plain, (![B_240, A_241]: (m1_pre_topc(k1_pre_topc(B_240, '#skF_2'(A_241, B_240)), B_240) | m1_pre_topc(B_240, A_241) | ~r1_tarski(k2_struct_0(B_240), k2_struct_0(A_241)) | ~l1_pre_topc(B_240) | ~l1_pre_topc(A_241))), inference(resolution, [status(thm)], [c_463, c_46])).
% 44.22/28.23  tff(c_3778, plain, (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5')), '#skF_5') | m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2580, c_3756])).
% 44.22/28.23  tff(c_3837, plain, (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5')), '#skF_5') | m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3778])).
% 44.22/28.23  tff(c_3838, plain, (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2537, c_3837])).
% 44.22/28.23  tff(c_3876, plain, (k2_struct_0(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5')))='#skF_2'('#skF_5', '#skF_5') | ~v1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5'))) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_3838, c_14])).
% 44.22/28.23  tff(c_3882, plain, (k2_struct_0(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5')))='#skF_2'('#skF_5', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_5', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_102, c_3437, c_3876])).
% 44.22/28.23  tff(c_7260, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_3882])).
% 44.22/28.23  tff(c_7263, plain, (m1_pre_topc('#skF_5', '#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_501, c_7260])).
% 44.22/28.23  tff(c_7266, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2580, c_7263])).
% 44.22/28.23  tff(c_7268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2537, c_7266])).
% 44.22/28.23  tff(c_7270, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_3882])).
% 44.22/28.23  tff(c_1360, plain, (![A_163, B_164, C_165]: (m1_subset_1('#skF_1'(A_163, B_164, C_165), k1_zfmisc_1(u1_struct_0(A_163))) | ~r2_hidden(C_165, u1_pre_topc(B_164)) | ~m1_subset_1(C_165, k1_zfmisc_1(u1_struct_0(B_164))) | ~m1_pre_topc(B_164, A_163) | ~l1_pre_topc(B_164) | ~l1_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_78])).
% 44.22/28.23  tff(c_4270, plain, (![A_259, B_260, C_261]: (v1_pre_topc(k1_pre_topc(A_259, '#skF_1'(A_259, B_260, C_261))) | ~r2_hidden(C_261, u1_pre_topc(B_260)) | ~m1_subset_1(C_261, k1_zfmisc_1(u1_struct_0(B_260))) | ~m1_pre_topc(B_260, A_259) | ~l1_pre_topc(B_260) | ~l1_pre_topc(A_259))), inference(resolution, [status(thm)], [c_1360, c_48])).
% 44.22/28.23  tff(c_4298, plain, (![A_259, C_261]: (v1_pre_topc(k1_pre_topc(A_259, '#skF_1'(A_259, '#skF_5', C_261))) | ~r2_hidden(C_261, u1_pre_topc('#skF_5')) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', A_259) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_259))), inference(superposition, [status(thm), theory('equality')], [c_102, c_4270])).
% 44.22/28.23  tff(c_4323, plain, (![A_259, C_261]: (v1_pre_topc(k1_pre_topc(A_259, '#skF_1'(A_259, '#skF_5', C_261))) | ~r2_hidden(C_261, u1_pre_topc('#skF_5')) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', A_259) | ~l1_pre_topc(A_259))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4298])).
% 44.22/28.23  tff(c_7300, plain, (![A_259]: (v1_pre_topc(k1_pre_topc(A_259, '#skF_1'(A_259, '#skF_5', '#skF_2'('#skF_5', '#skF_5')))) | ~r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5')) | ~m1_pre_topc('#skF_5', A_259) | ~l1_pre_topc(A_259))), inference(resolution, [status(thm)], [c_7270, c_4323])).
% 44.22/28.23  tff(c_15652, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5'))), inference(splitLeft, [status(thm)], [c_7300])).
% 44.22/28.23  tff(c_1834, plain, (![A_184, B_185]: (r2_hidden('#skF_2'(A_184, B_185), u1_pre_topc(B_185)) | k9_subset_1(u1_struct_0(B_185), '#skF_3'(A_184, B_185), k2_struct_0(B_185))='#skF_2'(A_184, B_185) | m1_pre_topc(B_185, A_184) | ~r1_tarski(k2_struct_0(B_185), k2_struct_0(A_184)) | ~l1_pre_topc(B_185) | ~l1_pre_topc(A_184))), inference(cnfTransformation, [status(thm)], [f_78])).
% 44.22/28.23  tff(c_1882, plain, (![A_184]: (r2_hidden('#skF_2'(A_184, '#skF_5'), u1_pre_topc('#skF_5')) | k9_subset_1(k2_struct_0('#skF_5'), '#skF_3'(A_184, '#skF_5'), k2_struct_0('#skF_5'))='#skF_2'(A_184, '#skF_5') | m1_pre_topc('#skF_5', A_184) | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0(A_184)) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_184))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1834])).
% 44.22/28.23  tff(c_1911, plain, (![A_184]: (r2_hidden('#skF_2'(A_184, '#skF_5'), u1_pre_topc('#skF_5')) | k3_xboole_0('#skF_3'(A_184, '#skF_5'), k2_struct_0('#skF_5'))='#skF_2'(A_184, '#skF_5') | m1_pre_topc('#skF_5', A_184) | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0(A_184)) | ~l1_pre_topc(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_181, c_1882])).
% 44.22/28.23  tff(c_15675, plain, (k3_xboole_0('#skF_3'('#skF_5', '#skF_5'), k2_struct_0('#skF_5'))='#skF_2'('#skF_5', '#skF_5') | m1_pre_topc('#skF_5', '#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1911, c_15652])).
% 44.22/28.23  tff(c_15701, plain, (k3_xboole_0('#skF_3'('#skF_5', '#skF_5'), k2_struct_0('#skF_5'))='#skF_2'('#skF_5', '#skF_5') | m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2580, c_15675])).
% 44.22/28.23  tff(c_15702, plain, (k3_xboole_0('#skF_3'('#skF_5', '#skF_5'), k2_struct_0('#skF_5'))='#skF_2'('#skF_5', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2537, c_15701])).
% 44.22/28.23  tff(c_1463, plain, (![A_170, B_171]: (r2_hidden('#skF_2'(A_170, B_171), u1_pre_topc(B_171)) | m1_subset_1('#skF_3'(A_170, B_171), k1_zfmisc_1(u1_struct_0(A_170))) | m1_pre_topc(B_171, A_170) | ~r1_tarski(k2_struct_0(B_171), k2_struct_0(A_170)) | ~l1_pre_topc(B_171) | ~l1_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_78])).
% 44.22/28.23  tff(c_1495, plain, (![A_170, B_171]: (m1_pre_topc(k1_pre_topc(A_170, '#skF_3'(A_170, B_171)), A_170) | r2_hidden('#skF_2'(A_170, B_171), u1_pre_topc(B_171)) | m1_pre_topc(B_171, A_170) | ~r1_tarski(k2_struct_0(B_171), k2_struct_0(A_170)) | ~l1_pre_topc(B_171) | ~l1_pre_topc(A_170))), inference(resolution, [status(thm)], [c_1463, c_46])).
% 44.22/28.23  tff(c_15669, plain, (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5')), '#skF_5') | m1_pre_topc('#skF_5', '#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1495, c_15652])).
% 44.22/28.23  tff(c_15693, plain, (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5')), '#skF_5') | m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2580, c_15669])).
% 44.22/28.23  tff(c_15694, plain, (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2537, c_15693])).
% 44.22/28.23  tff(c_4669, plain, (![A_283, B_284]: (m1_pre_topc(k1_pre_topc(A_283, '#skF_3'(A_283, B_284)), A_283) | r2_hidden('#skF_2'(A_283, B_284), u1_pre_topc(B_284)) | m1_pre_topc(B_284, A_283) | ~r1_tarski(k2_struct_0(B_284), k2_struct_0(A_283)) | ~l1_pre_topc(B_284) | ~l1_pre_topc(A_283))), inference(resolution, [status(thm)], [c_1463, c_46])).
% 44.22/28.23  tff(c_4718, plain, (![A_283, B_284]: (l1_pre_topc(k1_pre_topc(A_283, '#skF_3'(A_283, B_284))) | r2_hidden('#skF_2'(A_283, B_284), u1_pre_topc(B_284)) | m1_pre_topc(B_284, A_283) | ~r1_tarski(k2_struct_0(B_284), k2_struct_0(A_283)) | ~l1_pre_topc(B_284) | ~l1_pre_topc(A_283))), inference(resolution, [status(thm)], [c_4669, c_52])).
% 44.22/28.23  tff(c_15655, plain, (l1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5'))) | m1_pre_topc('#skF_5', '#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_4718, c_15652])).
% 44.22/28.23  tff(c_15681, plain, (l1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5'))) | m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2580, c_15655])).
% 44.22/28.23  tff(c_15682, plain, (l1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2537, c_15681])).
% 44.22/28.23  tff(c_1493, plain, (![B_171]: (r2_hidden('#skF_2'('#skF_5', B_171), u1_pre_topc(B_171)) | m1_subset_1('#skF_3'('#skF_5', B_171), k1_zfmisc_1(k2_struct_0('#skF_5'))) | m1_pre_topc(B_171, '#skF_5') | ~r1_tarski(k2_struct_0(B_171), k2_struct_0('#skF_5')) | ~l1_pre_topc(B_171) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1463])).
% 44.22/28.23  tff(c_1509, plain, (![B_171]: (r2_hidden('#skF_2'('#skF_5', B_171), u1_pre_topc(B_171)) | m1_subset_1('#skF_3'('#skF_5', B_171), k1_zfmisc_1(k2_struct_0('#skF_5'))) | m1_pre_topc(B_171, '#skF_5') | ~r1_tarski(k2_struct_0(B_171), k2_struct_0('#skF_5')) | ~l1_pre_topc(B_171))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1493])).
% 44.22/28.23  tff(c_1497, plain, (![A_170, B_171]: (v1_pre_topc(k1_pre_topc(A_170, '#skF_3'(A_170, B_171))) | r2_hidden('#skF_2'(A_170, B_171), u1_pre_topc(B_171)) | m1_pre_topc(B_171, A_170) | ~r1_tarski(k2_struct_0(B_171), k2_struct_0(A_170)) | ~l1_pre_topc(B_171) | ~l1_pre_topc(A_170))), inference(resolution, [status(thm)], [c_1463, c_48])).
% 44.22/28.23  tff(c_15672, plain, (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5'))) | m1_pre_topc('#skF_5', '#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1497, c_15652])).
% 44.22/28.23  tff(c_15697, plain, (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5'))) | m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2580, c_15672])).
% 44.22/28.23  tff(c_15698, plain, (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2537, c_15697])).
% 44.22/28.23  tff(c_15708, plain, (k2_struct_0(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5')))='#skF_3'('#skF_5', '#skF_5') | ~v1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5'))) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_15694, c_14])).
% 44.22/28.23  tff(c_15714, plain, (k2_struct_0(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5')))='#skF_3'('#skF_5', '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_102, c_15698, c_15708])).
% 44.22/28.23  tff(c_16336, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_15714])).
% 44.22/28.23  tff(c_16339, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5')) | m1_pre_topc('#skF_5', '#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1509, c_16336])).
% 44.22/28.23  tff(c_16342, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5')) | m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2580, c_16339])).
% 44.22/28.23  tff(c_16344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2537, c_15652, c_16342])).
% 44.22/28.23  tff(c_16345, plain, (k2_struct_0(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5')))='#skF_3'('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_15714])).
% 44.22/28.23  tff(c_16506, plain, (![A_121]: (k3_xboole_0('#skF_3'('#skF_5', '#skF_5'), k2_struct_0(A_121))=k2_struct_0(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5'))) | ~m1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5')), A_121) | ~l1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5'))) | ~l1_pre_topc(A_121))), inference(superposition, [status(thm), theory('equality')], [c_16345, c_224])).
% 44.22/28.23  tff(c_18262, plain, (![A_658]: (k3_xboole_0('#skF_3'('#skF_5', '#skF_5'), k2_struct_0(A_658))='#skF_3'('#skF_5', '#skF_5') | ~m1_pre_topc(k1_pre_topc('#skF_5', '#skF_3'('#skF_5', '#skF_5')), A_658) | ~l1_pre_topc(A_658))), inference(demodulation, [status(thm), theory('equality')], [c_15682, c_16345, c_16506])).
% 44.22/28.23  tff(c_18265, plain, (k3_xboole_0('#skF_3'('#skF_5', '#skF_5'), k2_struct_0('#skF_5'))='#skF_3'('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_15694, c_18262])).
% 44.22/28.23  tff(c_18270, plain, ('#skF_3'('#skF_5', '#skF_5')='#skF_2'('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_15702, c_18265])).
% 44.22/28.23  tff(c_30, plain, (![A_18, B_40]: (r2_hidden('#skF_2'(A_18, B_40), u1_pre_topc(B_40)) | r2_hidden('#skF_3'(A_18, B_40), u1_pre_topc(A_18)) | m1_pre_topc(B_40, A_18) | ~r1_tarski(k2_struct_0(B_40), k2_struct_0(A_18)) | ~l1_pre_topc(B_40) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 44.22/28.23  tff(c_16346, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_15714])).
% 44.22/28.23  tff(c_16400, plain, (![A_259]: (v1_pre_topc(k1_pre_topc(A_259, '#skF_1'(A_259, '#skF_5', '#skF_3'('#skF_5', '#skF_5')))) | ~r2_hidden('#skF_3'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5')) | ~m1_pre_topc('#skF_5', A_259) | ~l1_pre_topc(A_259))), inference(resolution, [status(thm)], [c_16346, c_4323])).
% 44.22/28.23  tff(c_18271, plain, (~r2_hidden('#skF_3'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5'))), inference(splitLeft, [status(thm)], [c_16400])).
% 44.22/28.23  tff(c_18274, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5')) | m1_pre_topc('#skF_5', '#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_30, c_18271])).
% 44.22/28.23  tff(c_18277, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5')) | m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2580, c_18274])).
% 44.22/28.23  tff(c_18279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2537, c_15652, c_18277])).
% 44.22/28.23  tff(c_18281, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5'))), inference(splitRight, [status(thm)], [c_16400])).
% 44.22/28.23  tff(c_18288, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18270, c_18281])).
% 44.22/28.23  tff(c_18324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15652, c_18288])).
% 44.22/28.23  tff(c_18326, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5'))), inference(splitRight, [status(thm)], [c_7300])).
% 44.22/28.23  tff(c_3879, plain, (l1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_3838, c_52])).
% 44.22/28.23  tff(c_3885, plain, (l1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3879])).
% 44.22/28.23  tff(c_7269, plain, (k2_struct_0(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5')))='#skF_2'('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_3882])).
% 44.22/28.23  tff(c_7383, plain, (![A_121]: (k3_xboole_0('#skF_2'('#skF_5', '#skF_5'), k2_struct_0(A_121))=k2_struct_0(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5'))) | ~m1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5')), A_121) | ~l1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5'))) | ~l1_pre_topc(A_121))), inference(superposition, [status(thm), theory('equality')], [c_7269, c_224])).
% 44.22/28.23  tff(c_13202, plain, (![A_546]: (k3_xboole_0('#skF_2'('#skF_5', '#skF_5'), k2_struct_0(A_546))='#skF_2'('#skF_5', '#skF_5') | ~m1_pre_topc(k1_pre_topc('#skF_5', '#skF_2'('#skF_5', '#skF_5')), A_546) | ~l1_pre_topc(A_546))), inference(demodulation, [status(thm), theory('equality')], [c_3885, c_7269, c_7383])).
% 44.22/28.23  tff(c_13209, plain, (k3_xboole_0('#skF_2'('#skF_5', '#skF_5'), k2_struct_0('#skF_5'))='#skF_2'('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_3838, c_13202])).
% 44.22/28.23  tff(c_13216, plain, (k3_xboole_0('#skF_2'('#skF_5', '#skF_5'), k2_struct_0('#skF_5'))='#skF_2'('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_13209])).
% 44.22/28.23  tff(c_2460, plain, (![B_201, D_202, A_203]: (k9_subset_1(u1_struct_0(B_201), D_202, k2_struct_0(B_201))!='#skF_2'(A_203, B_201) | ~r2_hidden(D_202, u1_pre_topc(A_203)) | ~m1_subset_1(D_202, k1_zfmisc_1(u1_struct_0(A_203))) | ~r2_hidden('#skF_2'(A_203, B_201), u1_pre_topc(B_201)) | m1_pre_topc(B_201, A_203) | ~r1_tarski(k2_struct_0(B_201), k2_struct_0(A_203)) | ~l1_pre_topc(B_201) | ~l1_pre_topc(A_203))), inference(cnfTransformation, [status(thm)], [f_78])).
% 44.22/28.23  tff(c_2500, plain, (![D_202, A_203]: (k9_subset_1(k2_struct_0('#skF_5'), D_202, k2_struct_0('#skF_5'))!='#skF_2'(A_203, '#skF_5') | ~r2_hidden(D_202, u1_pre_topc(A_203)) | ~m1_subset_1(D_202, k1_zfmisc_1(u1_struct_0(A_203))) | ~r2_hidden('#skF_2'(A_203, '#skF_5'), u1_pre_topc('#skF_5')) | m1_pre_topc('#skF_5', A_203) | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0(A_203)) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_203))), inference(superposition, [status(thm), theory('equality')], [c_102, c_2460])).
% 44.22/28.23  tff(c_3049, plain, (![D_230, A_231]: (k3_xboole_0(D_230, k2_struct_0('#skF_5'))!='#skF_2'(A_231, '#skF_5') | ~r2_hidden(D_230, u1_pre_topc(A_231)) | ~m1_subset_1(D_230, k1_zfmisc_1(u1_struct_0(A_231))) | ~r2_hidden('#skF_2'(A_231, '#skF_5'), u1_pre_topc('#skF_5')) | m1_pre_topc('#skF_5', A_231) | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0(A_231)) | ~l1_pre_topc(A_231))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_181, c_2500])).
% 44.22/28.23  tff(c_3075, plain, (![D_230]: (k3_xboole_0(D_230, k2_struct_0('#skF_5'))!='#skF_2'('#skF_5', '#skF_5') | ~r2_hidden(D_230, u1_pre_topc('#skF_5')) | ~m1_subset_1(D_230, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5')) | m1_pre_topc('#skF_5', '#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_3049])).
% 44.22/28.23  tff(c_3098, plain, (![D_230]: (k3_xboole_0(D_230, k2_struct_0('#skF_5'))!='#skF_2'('#skF_5', '#skF_5') | ~r2_hidden(D_230, u1_pre_topc('#skF_5')) | ~m1_subset_1(D_230, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5')) | m1_pre_topc('#skF_5', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2580, c_3075])).
% 44.22/28.23  tff(c_3099, plain, (![D_230]: (k3_xboole_0(D_230, k2_struct_0('#skF_5'))!='#skF_2'('#skF_5', '#skF_5') | ~r2_hidden(D_230, u1_pre_topc('#skF_5')) | ~m1_subset_1(D_230, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2537, c_3098])).
% 44.22/28.23  tff(c_22546, plain, (![D_734]: (k3_xboole_0(D_734, k2_struct_0('#skF_5'))!='#skF_2'('#skF_5', '#skF_5') | ~r2_hidden(D_734, u1_pre_topc('#skF_5')) | ~m1_subset_1(D_734, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_18326, c_3099])).
% 44.22/28.23  tff(c_22549, plain, (k3_xboole_0('#skF_2'('#skF_5', '#skF_5'), k2_struct_0('#skF_5'))!='#skF_2'('#skF_5', '#skF_5') | ~r2_hidden('#skF_2'('#skF_5', '#skF_5'), u1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_7270, c_22546])).
% 44.22/28.23  tff(c_22572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18326, c_13216, c_22549])).
% 44.22/28.23  tff(c_22574, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_2455])).
% 44.22/28.23  tff(c_64, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.22/28.23  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.22/28.23  tff(c_76, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_72])).
% 44.22/28.23  tff(c_103, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_76])).
% 44.22/28.23  tff(c_68, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 44.22/28.23  tff(c_75, plain, (v3_pre_topc('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68])).
% 44.22/28.23  tff(c_634, plain, (![A_139, B_140, C_141]: (m1_subset_1('#skF_4'(A_139, B_140, C_141), k1_zfmisc_1(u1_struct_0(A_139))) | ~v3_pre_topc(C_141, B_140) | ~m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0(B_140))) | ~m1_pre_topc(B_140, A_139) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_114])).
% 44.22/28.23  tff(c_664, plain, (![B_140, C_141]: (m1_subset_1('#skF_4'('#skF_5', B_140, C_141), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~v3_pre_topc(C_141, B_140) | ~m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0(B_140))) | ~m1_pre_topc(B_140, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_634])).
% 44.22/28.23  tff(c_1221, plain, (![B_156, C_157]: (m1_subset_1('#skF_4'('#skF_5', B_156, C_157), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~v3_pre_topc(C_157, B_156) | ~m1_subset_1(C_157, k1_zfmisc_1(u1_struct_0(B_156))) | ~m1_pre_topc(B_156, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_664])).
% 44.22/28.23  tff(c_229, plain, (![B_123]: (m1_pre_topc(k1_pre_topc('#skF_5', B_123), '#skF_5') | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_225])).
% 44.22/28.23  tff(c_236, plain, (![B_123]: (m1_pre_topc(k1_pre_topc('#skF_5', B_123), '#skF_5') | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_229])).
% 44.22/28.23  tff(c_47993, plain, (![B_1407, C_1408]: (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', B_1407, C_1408)), '#skF_5') | ~v3_pre_topc(C_1408, B_1407) | ~m1_subset_1(C_1408, k1_zfmisc_1(u1_struct_0(B_1407))) | ~m1_pre_topc(B_1407, '#skF_5'))), inference(resolution, [status(thm)], [c_1221, c_236])).
% 44.22/28.23  tff(c_48050, plain, (![C_1408]: (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', C_1408)), '#skF_5') | ~v3_pre_topc(C_1408, '#skF_5') | ~m1_subset_1(C_1408, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_47993])).
% 44.22/28.23  tff(c_48086, plain, (![C_1410]: (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', C_1410)), '#skF_5') | ~v3_pre_topc(C_1410, '#skF_5') | ~m1_subset_1(C_1410, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_22574, c_48050])).
% 44.22/28.23  tff(c_48101, plain, (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8')), '#skF_5') | ~v3_pre_topc('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_103, c_48086])).
% 44.22/28.23  tff(c_48112, plain, (m1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_48101])).
% 44.22/28.23  tff(c_48125, plain, (l1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48112, c_52])).
% 44.22/28.23  tff(c_48131, plain, (l1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48125])).
% 44.22/28.23  tff(c_680, plain, (![B_140, C_141]: (m1_subset_1('#skF_4'('#skF_5', B_140, C_141), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~v3_pre_topc(C_141, B_140) | ~m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0(B_140))) | ~m1_pre_topc(B_140, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_664])).
% 44.22/28.23  tff(c_140, plain, (![B_109]: (v1_pre_topc(k1_pre_topc('#skF_5', B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_134])).
% 44.22/28.23  tff(c_148, plain, (![B_109]: (v1_pre_topc(k1_pre_topc('#skF_5', B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_140])).
% 44.22/28.23  tff(c_29589, plain, (![B_966, C_967]: (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', B_966, C_967))) | ~v3_pre_topc(C_967, B_966) | ~m1_subset_1(C_967, k1_zfmisc_1(u1_struct_0(B_966))) | ~m1_pre_topc(B_966, '#skF_5'))), inference(resolution, [status(thm)], [c_1221, c_148])).
% 44.22/28.23  tff(c_29646, plain, (![C_967]: (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', C_967))) | ~v3_pre_topc(C_967, '#skF_5') | ~m1_subset_1(C_967, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_29589])).
% 44.22/28.23  tff(c_29678, plain, (![C_969]: (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', C_969))) | ~v3_pre_topc(C_969, '#skF_5') | ~m1_subset_1(C_969, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_22574, c_29646])).
% 44.22/28.23  tff(c_29693, plain, (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8'))) | ~v3_pre_topc('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_103, c_29678])).
% 44.22/28.23  tff(c_29704, plain, (v1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_29693])).
% 44.22/28.23  tff(c_48122, plain, (k2_struct_0(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8')))='#skF_4'('#skF_5', '#skF_5', '#skF_8') | ~v1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8'))) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_5', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48112, c_14])).
% 44.22/28.23  tff(c_48128, plain, (k2_struct_0(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8')))='#skF_4'('#skF_5', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_4'('#skF_5', '#skF_5', '#skF_8'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_102, c_29704, c_48122])).
% 44.22/28.23  tff(c_49943, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_5', '#skF_8'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_48128])).
% 44.22/28.23  tff(c_49946, plain, (~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_680, c_49943])).
% 44.22/28.23  tff(c_49950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22574, c_103, c_102, c_75, c_49946])).
% 44.22/28.23  tff(c_49951, plain, (k2_struct_0(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8')))='#skF_4'('#skF_5', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_48128])).
% 44.22/28.23  tff(c_50102, plain, (![A_121]: (k3_xboole_0('#skF_4'('#skF_5', '#skF_5', '#skF_8'), k2_struct_0(A_121))=k2_struct_0(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8'))) | ~m1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8')), A_121) | ~l1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8'))) | ~l1_pre_topc(A_121))), inference(superposition, [status(thm), theory('equality')], [c_49951, c_224])).
% 44.22/28.23  tff(c_75513, plain, (![A_1872]: (k3_xboole_0('#skF_4'('#skF_5', '#skF_5', '#skF_8'), k2_struct_0(A_1872))='#skF_4'('#skF_5', '#skF_5', '#skF_8') | ~m1_pre_topc(k1_pre_topc('#skF_5', '#skF_4'('#skF_5', '#skF_5', '#skF_8')), A_1872) | ~l1_pre_topc(A_1872))), inference(demodulation, [status(thm), theory('equality')], [c_48131, c_49951, c_50102])).
% 44.22/28.23  tff(c_75516, plain, (k3_xboole_0('#skF_4'('#skF_5', '#skF_5', '#skF_8'), k2_struct_0('#skF_5'))='#skF_4'('#skF_5', '#skF_5', '#skF_8') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_48112, c_75513])).
% 44.22/28.23  tff(c_75523, plain, (k3_xboole_0('#skF_4'('#skF_5', '#skF_5', '#skF_8'), k2_struct_0('#skF_5'))='#skF_4'('#skF_5', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_75516])).
% 44.22/28.23  tff(c_959, plain, (![B_149, A_150, C_151]: (k9_subset_1(u1_struct_0(B_149), '#skF_4'(A_150, B_149, C_151), k2_struct_0(B_149))=C_151 | ~v3_pre_topc(C_151, B_149) | ~m1_subset_1(C_151, k1_zfmisc_1(u1_struct_0(B_149))) | ~m1_pre_topc(B_149, A_150) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_114])).
% 44.22/28.23  tff(c_992, plain, (![A_150, C_151]: (k9_subset_1(k2_struct_0('#skF_5'), '#skF_4'(A_150, '#skF_5', C_151), k2_struct_0('#skF_5'))=C_151 | ~v3_pre_topc(C_151, '#skF_5') | ~m1_subset_1(C_151, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', A_150) | ~l1_pre_topc(A_150))), inference(superposition, [status(thm), theory('equality')], [c_102, c_959])).
% 44.22/28.23  tff(c_1293, plain, (![A_160, C_161]: (k3_xboole_0('#skF_4'(A_160, '#skF_5', C_161), k2_struct_0('#skF_5'))=C_161 | ~v3_pre_topc(C_161, '#skF_5') | ~m1_subset_1(C_161, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', A_160) | ~l1_pre_topc(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_181, c_992])).
% 44.22/28.23  tff(c_1299, plain, (![A_160]: (k3_xboole_0('#skF_4'(A_160, '#skF_5', '#skF_8'), k2_struct_0('#skF_5'))='#skF_8' | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_pre_topc('#skF_5', A_160) | ~l1_pre_topc(A_160))), inference(resolution, [status(thm)], [c_103, c_1293])).
% 44.22/28.23  tff(c_1307, plain, (![A_160]: (k3_xboole_0('#skF_4'(A_160, '#skF_5', '#skF_8'), k2_struct_0('#skF_5'))='#skF_8' | ~m1_pre_topc('#skF_5', A_160) | ~l1_pre_topc(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1299])).
% 44.22/28.23  tff(c_75536, plain, ('#skF_4'('#skF_5', '#skF_5', '#skF_8')='#skF_8' | ~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_75523, c_1307])).
% 44.22/28.23  tff(c_75548, plain, ('#skF_4'('#skF_5', '#skF_5', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_22574, c_75536])).
% 44.22/28.23  tff(c_60, plain, (![A_64, B_76, C_82]: (m1_subset_1('#skF_4'(A_64, B_76, C_82), k1_zfmisc_1(u1_struct_0(A_64))) | ~v3_pre_topc(C_82, B_76) | ~m1_subset_1(C_82, k1_zfmisc_1(u1_struct_0(B_76))) | ~m1_pre_topc(B_76, A_64) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_114])).
% 44.22/28.23  tff(c_2030, plain, (![B_187, A_64, B_76, C_82]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_187), '#skF_4'(A_64, B_76, C_82), k2_struct_0(B_187)), B_187) | ~v3_pre_topc('#skF_4'(A_64, B_76, C_82), A_64) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_187), '#skF_4'(A_64, B_76, C_82), k2_struct_0(B_187)), k1_zfmisc_1(u1_struct_0(B_187))) | ~m1_pre_topc(B_187, A_64) | ~v3_pre_topc(C_82, B_76) | ~m1_subset_1(C_82, k1_zfmisc_1(u1_struct_0(B_76))) | ~m1_pre_topc(B_76, A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_60, c_1994])).
% 44.22/28.23  tff(c_75680, plain, (![B_187]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_187), '#skF_4'('#skF_5', '#skF_5', '#skF_8'), k2_struct_0(B_187)), B_187) | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(k9_subset_1(u1_struct_0(B_187), '#skF_4'('#skF_5', '#skF_5', '#skF_8'), k2_struct_0(B_187)), k1_zfmisc_1(u1_struct_0(B_187))) | ~m1_pre_topc(B_187, '#skF_5') | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_75548, c_2030])).
% 44.22/28.23  tff(c_77707, plain, (![B_1903]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_1903), '#skF_8', k2_struct_0(B_1903)), B_1903) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_1903), '#skF_8', k2_struct_0(B_1903)), k1_zfmisc_1(u1_struct_0(B_1903))) | ~m1_pre_topc(B_1903, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_22574, c_103, c_102, c_75, c_75548, c_75, c_75548, c_75680])).
% 44.22/28.23  tff(c_77905, plain, (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', k2_struct_0('#skF_7')), '#skF_7') | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_7'), '#skF_8', k2_struct_0('#skF_7')), k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~m1_pre_topc('#skF_7', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_119, c_77707])).
% 44.22/28.23  tff(c_78007, plain, (v3_pre_topc('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_120, c_119, c_1816, c_181, c_1816, c_181, c_119, c_77905])).
% 44.22/28.23  tff(c_78009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_78007])).
% 44.22/28.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 44.22/28.23  
% 44.22/28.23  Inference rules
% 44.22/28.23  ----------------------
% 44.22/28.23  #Ref     : 0
% 44.22/28.23  #Sup     : 17170
% 44.22/28.23  #Fact    : 0
% 44.22/28.23  #Define  : 0
% 44.22/28.23  #Split   : 320
% 44.22/28.23  #Chain   : 0
% 44.22/28.23  #Close   : 0
% 44.22/28.23  
% 44.22/28.23  Ordering : KBO
% 44.22/28.23  
% 44.22/28.23  Simplification rules
% 44.22/28.23  ----------------------
% 44.22/28.23  #Subsume      : 1805
% 44.22/28.23  #Demod        : 29567
% 44.22/28.23  #Tautology    : 2261
% 44.22/28.23  #SimpNegUnit  : 391
% 44.22/28.23  #BackRed      : 162
% 44.22/28.23  
% 44.22/28.23  #Partial instantiations: 0
% 44.22/28.23  #Strategies tried      : 1
% 44.22/28.23  
% 44.22/28.23  Timing (in seconds)
% 44.22/28.23  ----------------------
% 44.22/28.24  Preprocessing        : 0.58
% 44.22/28.24  Parsing              : 0.28
% 44.22/28.24  CNF conversion       : 0.05
% 44.22/28.24  Main loop            : 26.69
% 44.22/28.24  Inferencing          : 4.25
% 44.22/28.24  Reduction            : 12.23
% 44.22/28.24  Demodulation         : 9.73
% 44.22/28.24  BG Simplification    : 0.48
% 44.22/28.24  Subsumption          : 8.52
% 44.22/28.24  Abstraction          : 0.84
% 44.22/28.24  MUC search           : 0.00
% 44.22/28.24  Cooper               : 0.00
% 44.22/28.24  Total                : 27.35
% 44.22/28.24  Index Insertion      : 0.00
% 44.22/28.24  Index Deletion       : 0.00
% 44.22/28.24  Index Matching       : 0.00
% 44.22/28.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
