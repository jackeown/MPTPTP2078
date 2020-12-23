%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:12 EST 2020

% Result     : Theorem 9.11s
% Output     : CNFRefutation 9.30s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 116 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 250 expanded)
%              Number of equality atoms :    9 (  25 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_96,plain,(
    ! [A_43,B_44,C_45] :
      ( k9_subset_1(A_43,B_44,C_45) = k3_xboole_0(B_44,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    ! [B_44] : k9_subset_1(u1_struct_0('#skF_1'),B_44,'#skF_3') = k3_xboole_0(B_44,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_96])).

tff(c_137,plain,(
    ! [A_50,B_51,C_52] :
      ( m1_subset_1(k9_subset_1(A_50,B_51,C_52),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    ! [B_44] :
      ( m1_subset_1(k3_xboole_0(B_44,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_137])).

tff(c_155,plain,(
    ! [B_44] : m1_subset_1(k3_xboole_0(B_44,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_145])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k3_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_249,plain,(
    ! [C_69,A_70,B_71] :
      ( v2_tex_2(C_69,A_70)
      | ~ v2_tex_2(B_71,A_70)
      | ~ r1_tarski(C_69,B_71)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_483,plain,(
    ! [A_104,C_105,A_106,B_107] :
      ( v2_tex_2(k3_xboole_0(A_104,C_105),A_106)
      | ~ v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(k3_xboole_0(A_104,C_105),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ r1_tarski(A_104,B_107) ) ),
    inference(resolution,[status(thm)],[c_8,c_249])).

tff(c_494,plain,(
    ! [B_44,B_107] :
      ( v2_tex_2(k3_xboole_0(B_44,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_107,'#skF_1')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(B_44,B_107) ) ),
    inference(resolution,[status(thm)],[c_155,c_483])).

tff(c_928,plain,(
    ! [B_168,B_169] :
      ( v2_tex_2(k3_xboole_0(B_168,'#skF_3'),'#skF_1')
      | ~ v2_tex_2(B_169,'#skF_1')
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(B_168,B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_494])).

tff(c_959,plain,(
    ! [B_168] :
      ( v2_tex_2(k3_xboole_0(B_168,'#skF_3'),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ r1_tarski(B_168,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_928])).

tff(c_979,plain,(
    ! [B_170] :
      ( v2_tex_2(k3_xboole_0(B_170,'#skF_3'),'#skF_1')
      | ~ r1_tarski(B_170,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_959])).

tff(c_26,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_127,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_26])).

tff(c_982,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_979,c_127])).

tff(c_986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_982])).

tff(c_987,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1034,plain,(
    ! [A_182,B_183,C_184] :
      ( k9_subset_1(A_182,B_183,C_184) = k3_xboole_0(B_183,C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(A_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1044,plain,(
    ! [B_183] : k9_subset_1(u1_struct_0('#skF_1'),B_183,'#skF_3') = k3_xboole_0(B_183,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1034])).

tff(c_1093,plain,(
    ! [A_192,B_193,C_194] :
      ( m1_subset_1(k9_subset_1(A_192,B_193,C_194),k1_zfmisc_1(A_192))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(A_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1101,plain,(
    ! [B_183] :
      ( m1_subset_1(k3_xboole_0(B_183,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_1093])).

tff(c_1111,plain,(
    ! [B_183] : m1_subset_1(k3_xboole_0(B_183,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1101])).

tff(c_10,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_35,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_1046,plain,(
    ! [A_7,B_183] : k9_subset_1(A_7,B_183,A_7) = k3_xboole_0(B_183,A_7) ),
    inference(resolution,[status(thm)],[c_35,c_1034])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1109,plain,(
    ! [A_192,B_193,C_194] :
      ( r1_tarski(k9_subset_1(A_192,B_193,C_194),A_192)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(A_192)) ) ),
    inference(resolution,[status(thm)],[c_1093,c_20])).

tff(c_1208,plain,(
    ! [C_211,A_212,B_213] :
      ( v2_tex_2(C_211,A_212)
      | ~ v2_tex_2(B_213,A_212)
      | ~ r1_tarski(C_211,B_213)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2526,plain,(
    ! [A_375,B_376,C_377,A_378] :
      ( v2_tex_2(k9_subset_1(A_375,B_376,C_377),A_378)
      | ~ v2_tex_2(A_375,A_378)
      | ~ m1_subset_1(k9_subset_1(A_375,B_376,C_377),k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ m1_subset_1(A_375,k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ l1_pre_topc(A_378)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(A_375)) ) ),
    inference(resolution,[status(thm)],[c_1109,c_1208])).

tff(c_2566,plain,(
    ! [A_7,B_183,A_378] :
      ( v2_tex_2(k9_subset_1(A_7,B_183,A_7),A_378)
      | ~ v2_tex_2(A_7,A_378)
      | ~ m1_subset_1(k3_xboole_0(B_183,A_7),k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ m1_subset_1(A_7,k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ l1_pre_topc(A_378)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1046,c_2526])).

tff(c_5034,plain,(
    ! [B_681,A_682,A_683] :
      ( v2_tex_2(k3_xboole_0(B_681,A_682),A_683)
      | ~ v2_tex_2(A_682,A_683)
      | ~ m1_subset_1(k3_xboole_0(B_681,A_682),k1_zfmisc_1(u1_struct_0(A_683)))
      | ~ m1_subset_1(A_682,k1_zfmisc_1(u1_struct_0(A_683)))
      | ~ l1_pre_topc(A_683) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_1046,c_2566])).

tff(c_5078,plain,(
    ! [B_183] :
      ( v2_tex_2(k3_xboole_0(B_183,'#skF_3'),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1111,c_5034])).

tff(c_5120,plain,(
    ! [B_183] : v2_tex_2(k3_xboole_0(B_183,'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_987,c_5078])).

tff(c_1067,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_26])).

tff(c_5172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5120,c_1067])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.32  % Computer   : n014.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 10:09:37 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.11/3.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.59  
% 9.11/3.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.60  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 9.11/3.60  
% 9.11/3.60  %Foreground sorts:
% 9.11/3.60  
% 9.11/3.60  
% 9.11/3.60  %Background operators:
% 9.11/3.60  
% 9.11/3.60  
% 9.11/3.60  %Foreground operators:
% 9.11/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.11/3.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.11/3.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.11/3.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.11/3.60  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.11/3.60  tff('#skF_2', type, '#skF_2': $i).
% 9.11/3.60  tff('#skF_3', type, '#skF_3': $i).
% 9.11/3.60  tff('#skF_1', type, '#skF_1': $i).
% 9.11/3.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.11/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.11/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.11/3.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.11/3.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.11/3.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.11/3.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.11/3.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.11/3.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.11/3.60  
% 9.30/3.62  tff(f_82, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 9.30/3.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.30/3.62  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.30/3.62  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 9.30/3.62  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 9.30/3.62  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 9.30/3.62  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 9.30/3.62  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.30/3.62  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.30/3.62  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.30/3.62  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.30/3.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.30/3.62  tff(c_28, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.30/3.62  tff(c_48, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 9.30/3.62  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.30/3.62  tff(c_96, plain, (![A_43, B_44, C_45]: (k9_subset_1(A_43, B_44, C_45)=k3_xboole_0(B_44, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.30/3.62  tff(c_106, plain, (![B_44]: (k9_subset_1(u1_struct_0('#skF_1'), B_44, '#skF_3')=k3_xboole_0(B_44, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_96])).
% 9.30/3.62  tff(c_137, plain, (![A_50, B_51, C_52]: (m1_subset_1(k9_subset_1(A_50, B_51, C_52), k1_zfmisc_1(A_50)) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.30/3.62  tff(c_145, plain, (![B_44]: (m1_subset_1(k3_xboole_0(B_44, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_106, c_137])).
% 9.30/3.62  tff(c_155, plain, (![B_44]: (m1_subset_1(k3_xboole_0(B_44, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_145])).
% 9.30/3.62  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k3_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.30/3.62  tff(c_249, plain, (![C_69, A_70, B_71]: (v2_tex_2(C_69, A_70) | ~v2_tex_2(B_71, A_70) | ~r1_tarski(C_69, B_71) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.30/3.62  tff(c_483, plain, (![A_104, C_105, A_106, B_107]: (v2_tex_2(k3_xboole_0(A_104, C_105), A_106) | ~v2_tex_2(B_107, A_106) | ~m1_subset_1(k3_xboole_0(A_104, C_105), k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~r1_tarski(A_104, B_107))), inference(resolution, [status(thm)], [c_8, c_249])).
% 9.30/3.62  tff(c_494, plain, (![B_44, B_107]: (v2_tex_2(k3_xboole_0(B_44, '#skF_3'), '#skF_1') | ~v2_tex_2(B_107, '#skF_1') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(B_44, B_107))), inference(resolution, [status(thm)], [c_155, c_483])).
% 9.30/3.62  tff(c_928, plain, (![B_168, B_169]: (v2_tex_2(k3_xboole_0(B_168, '#skF_3'), '#skF_1') | ~v2_tex_2(B_169, '#skF_1') | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(B_168, B_169))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_494])).
% 9.30/3.62  tff(c_959, plain, (![B_168]: (v2_tex_2(k3_xboole_0(B_168, '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~r1_tarski(B_168, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_928])).
% 9.30/3.62  tff(c_979, plain, (![B_170]: (v2_tex_2(k3_xboole_0(B_170, '#skF_3'), '#skF_1') | ~r1_tarski(B_170, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_959])).
% 9.30/3.62  tff(c_26, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.30/3.62  tff(c_127, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_26])).
% 9.30/3.62  tff(c_982, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_979, c_127])).
% 9.30/3.62  tff(c_986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_982])).
% 9.30/3.62  tff(c_987, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 9.30/3.62  tff(c_1034, plain, (![A_182, B_183, C_184]: (k9_subset_1(A_182, B_183, C_184)=k3_xboole_0(B_183, C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(A_182)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.30/3.62  tff(c_1044, plain, (![B_183]: (k9_subset_1(u1_struct_0('#skF_1'), B_183, '#skF_3')=k3_xboole_0(B_183, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_1034])).
% 9.30/3.62  tff(c_1093, plain, (![A_192, B_193, C_194]: (m1_subset_1(k9_subset_1(A_192, B_193, C_194), k1_zfmisc_1(A_192)) | ~m1_subset_1(C_194, k1_zfmisc_1(A_192)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.30/3.62  tff(c_1101, plain, (![B_183]: (m1_subset_1(k3_xboole_0(B_183, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1044, c_1093])).
% 9.30/3.62  tff(c_1111, plain, (![B_183]: (m1_subset_1(k3_xboole_0(B_183, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1101])).
% 9.30/3.62  tff(c_10, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.30/3.62  tff(c_12, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.30/3.62  tff(c_35, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 9.30/3.62  tff(c_1046, plain, (![A_7, B_183]: (k9_subset_1(A_7, B_183, A_7)=k3_xboole_0(B_183, A_7))), inference(resolution, [status(thm)], [c_35, c_1034])).
% 9.30/3.62  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.30/3.62  tff(c_1109, plain, (![A_192, B_193, C_194]: (r1_tarski(k9_subset_1(A_192, B_193, C_194), A_192) | ~m1_subset_1(C_194, k1_zfmisc_1(A_192)))), inference(resolution, [status(thm)], [c_1093, c_20])).
% 9.30/3.62  tff(c_1208, plain, (![C_211, A_212, B_213]: (v2_tex_2(C_211, A_212) | ~v2_tex_2(B_213, A_212) | ~r1_tarski(C_211, B_213) | ~m1_subset_1(C_211, k1_zfmisc_1(u1_struct_0(A_212))) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.30/3.62  tff(c_2526, plain, (![A_375, B_376, C_377, A_378]: (v2_tex_2(k9_subset_1(A_375, B_376, C_377), A_378) | ~v2_tex_2(A_375, A_378) | ~m1_subset_1(k9_subset_1(A_375, B_376, C_377), k1_zfmisc_1(u1_struct_0(A_378))) | ~m1_subset_1(A_375, k1_zfmisc_1(u1_struct_0(A_378))) | ~l1_pre_topc(A_378) | ~m1_subset_1(C_377, k1_zfmisc_1(A_375)))), inference(resolution, [status(thm)], [c_1109, c_1208])).
% 9.30/3.62  tff(c_2566, plain, (![A_7, B_183, A_378]: (v2_tex_2(k9_subset_1(A_7, B_183, A_7), A_378) | ~v2_tex_2(A_7, A_378) | ~m1_subset_1(k3_xboole_0(B_183, A_7), k1_zfmisc_1(u1_struct_0(A_378))) | ~m1_subset_1(A_7, k1_zfmisc_1(u1_struct_0(A_378))) | ~l1_pre_topc(A_378) | ~m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_1046, c_2526])).
% 9.30/3.62  tff(c_5034, plain, (![B_681, A_682, A_683]: (v2_tex_2(k3_xboole_0(B_681, A_682), A_683) | ~v2_tex_2(A_682, A_683) | ~m1_subset_1(k3_xboole_0(B_681, A_682), k1_zfmisc_1(u1_struct_0(A_683))) | ~m1_subset_1(A_682, k1_zfmisc_1(u1_struct_0(A_683))) | ~l1_pre_topc(A_683))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_1046, c_2566])).
% 9.30/3.62  tff(c_5078, plain, (![B_183]: (v2_tex_2(k3_xboole_0(B_183, '#skF_3'), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1111, c_5034])).
% 9.30/3.62  tff(c_5120, plain, (![B_183]: (v2_tex_2(k3_xboole_0(B_183, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_987, c_5078])).
% 9.30/3.62  tff(c_1067, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1044, c_26])).
% 9.30/3.62  tff(c_5172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5120, c_1067])).
% 9.30/3.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.30/3.62  
% 9.30/3.62  Inference rules
% 9.30/3.62  ----------------------
% 9.30/3.62  #Ref     : 0
% 9.30/3.62  #Sup     : 1210
% 9.30/3.62  #Fact    : 0
% 9.30/3.62  #Define  : 0
% 9.30/3.62  #Split   : 6
% 9.30/3.62  #Chain   : 0
% 9.30/3.62  #Close   : 0
% 9.30/3.62  
% 9.30/3.62  Ordering : KBO
% 9.30/3.62  
% 9.30/3.62  Simplification rules
% 9.30/3.62  ----------------------
% 9.30/3.62  #Subsume      : 97
% 9.30/3.62  #Demod        : 508
% 9.30/3.62  #Tautology    : 204
% 9.30/3.62  #SimpNegUnit  : 3
% 9.30/3.62  #BackRed      : 6
% 9.30/3.62  
% 9.30/3.62  #Partial instantiations: 0
% 9.30/3.62  #Strategies tried      : 1
% 9.30/3.62  
% 9.30/3.62  Timing (in seconds)
% 9.30/3.62  ----------------------
% 9.30/3.62  Preprocessing        : 0.45
% 9.30/3.62  Parsing              : 0.24
% 9.30/3.62  CNF conversion       : 0.03
% 9.30/3.62  Main loop            : 2.28
% 9.30/3.62  Inferencing          : 0.69
% 9.30/3.62  Reduction            : 0.69
% 9.30/3.62  Demodulation         : 0.50
% 9.30/3.62  BG Simplification    : 0.08
% 9.30/3.62  Subsumption          : 0.67
% 9.30/3.62  Abstraction          : 0.11
% 9.30/3.62  MUC search           : 0.00
% 9.30/3.62  Cooper               : 0.00
% 9.30/3.62  Total                : 2.78
% 9.30/3.62  Index Insertion      : 0.00
% 9.30/3.62  Index Deletion       : 0.00
% 9.30/3.63  Index Matching       : 0.00
% 9.30/3.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
