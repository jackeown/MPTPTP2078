%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:52 EST 2020

% Result     : Theorem 32.15s
% Output     : CNFRefutation 32.30s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 196 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 400 expanded)
%              Number of equality atoms :   15 (  56 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_132,plain,(
    ! [A_85,B_86,C_87] :
      ( k9_subset_1(A_85,B_86,C_87) = k3_xboole_0(B_86,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_170,plain,(
    ! [B_94,B_95,A_96] :
      ( k9_subset_1(B_94,B_95,A_96) = k3_xboole_0(B_95,A_96)
      | ~ r1_tarski(A_96,B_94) ) ),
    inference(resolution,[status(thm)],[c_32,c_132])).

tff(c_187,plain,(
    ! [B_2,B_95] : k9_subset_1(B_2,B_95,B_2) = k3_xboole_0(B_95,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_141,plain,(
    ! [B_86] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_86,'#skF_2') = k3_xboole_0(B_86,'#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_132])).

tff(c_280,plain,(
    ! [A_108,C_109,B_110] :
      ( k9_subset_1(A_108,C_109,B_110) = k9_subset_1(A_108,B_110,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_292,plain,(
    ! [B_110] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_110,'#skF_2') = k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',B_110) ),
    inference(resolution,[status(thm)],[c_46,c_280])).

tff(c_352,plain,(
    ! [B_112] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',B_112) = k3_xboole_0(B_112,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_292])).

tff(c_377,plain,(
    k3_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2') = k3_xboole_0('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_352])).

tff(c_215,plain,(
    ! [A_101,B_102,C_103] :
      ( m1_subset_1(k9_subset_1(A_101,B_102,C_103),k1_zfmisc_1(A_101))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_393,plain,(
    ! [A_113,B_114,C_115] :
      ( r1_tarski(k9_subset_1(A_113,B_114,C_115),A_113)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(A_113)) ) ),
    inference(resolution,[status(thm)],[c_215,c_30])).

tff(c_410,plain,(
    ! [B_95,B_2] :
      ( r1_tarski(k3_xboole_0(B_95,B_2),B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_393])).

tff(c_517,plain,
    ( r1_tarski(k3_xboole_0('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_410])).

tff(c_1034,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_1042,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1034])).

tff(c_1046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1042])).

tff(c_1048,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    ! [A_46] :
      ( l1_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_231,plain,(
    ! [A_101,B_102,C_103] :
      ( r1_tarski(k9_subset_1(A_101,B_102,C_103),A_101)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_101)) ) ),
    inference(resolution,[status(thm)],[c_215,c_30])).

tff(c_918,plain,(
    ! [C_154,A_155,B_156] :
      ( m1_subset_1(C_154,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155))))
      | ~ r1_tarski(C_154,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155))))
      | ~ l1_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_953,plain,(
    ! [A_101,B_102,C_103,A_155] :
      ( m1_subset_1(k9_subset_1(A_101,B_102,C_103),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155))))
      | ~ m1_subset_1(A_101,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155))))
      | ~ l1_struct_0(A_155)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_101)) ) ),
    inference(resolution,[status(thm)],[c_231,c_918])).

tff(c_1135,plain,(
    ! [B_164,A_165,C_166] :
      ( v2_tops_2(B_164,A_165)
      | ~ v2_tops_2(C_166,A_165)
      | ~ r1_tarski(B_164,C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_165))))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_165))))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6040,plain,(
    ! [A_302,B_303,C_304,A_305] :
      ( v2_tops_2(k9_subset_1(A_302,B_303,C_304),A_305)
      | ~ v2_tops_2(A_302,A_305)
      | ~ m1_subset_1(A_302,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_305))))
      | ~ m1_subset_1(k9_subset_1(A_302,B_303,C_304),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_305))))
      | ~ l1_pre_topc(A_305)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(A_302)) ) ),
    inference(resolution,[status(thm)],[c_231,c_1135])).

tff(c_77818,plain,(
    ! [A_1210,B_1211,C_1212,A_1213] :
      ( v2_tops_2(k9_subset_1(A_1210,B_1211,C_1212),A_1213)
      | ~ v2_tops_2(A_1210,A_1213)
      | ~ l1_pre_topc(A_1213)
      | ~ m1_subset_1(A_1210,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1213))))
      | ~ l1_struct_0(A_1213)
      | ~ m1_subset_1(C_1212,k1_zfmisc_1(A_1210)) ) ),
    inference(resolution,[status(thm)],[c_953,c_6040])).

tff(c_77893,plain,(
    ! [B_1211,C_1212] :
      ( v2_tops_2(k9_subset_1('#skF_2',B_1211,C_1212),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_struct_0('#skF_1')
      | ~ m1_subset_1(C_1212,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_46,c_77818])).

tff(c_77966,plain,(
    ! [B_1211,C_1212] :
      ( v2_tops_2(k9_subset_1('#skF_2',B_1211,C_1212),'#skF_1')
      | ~ l1_struct_0('#skF_1')
      | ~ m1_subset_1(C_1212,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_77893])).

tff(c_77967,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_77966])).

tff(c_77970,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_77967])).

tff(c_77974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_77970])).

tff(c_77980,plain,(
    ! [B_1214,C_1215] :
      ( v2_tops_2(k9_subset_1('#skF_2',B_1214,C_1215),'#skF_1')
      | ~ m1_subset_1(C_1215,k1_zfmisc_1('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_77966])).

tff(c_78048,plain,(
    ! [B_95] :
      ( v2_tops_2(k3_xboole_0(B_95,'#skF_2'),'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_77980])).

tff(c_78056,plain,(
    ! [B_95] : v2_tops_2(k3_xboole_0(B_95,'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_78048])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_140,plain,(
    ! [B_86] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_86,'#skF_3') = k3_xboole_0(B_86,'#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_132])).

tff(c_290,plain,(
    ! [B_110] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_110,'#skF_3') = k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3',B_110) ),
    inference(resolution,[status(thm)],[c_44,c_280])).

tff(c_301,plain,(
    ! [B_111] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_3',B_111) = k3_xboole_0(B_111,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_290])).

tff(c_315,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_141])).

tff(c_40,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_142,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_40])).

tff(c_340,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_142])).

tff(c_78059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78056,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.15/22.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.15/22.48  
% 32.15/22.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.15/22.48  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 32.15/22.48  
% 32.15/22.48  %Foreground sorts:
% 32.15/22.48  
% 32.15/22.48  
% 32.15/22.48  %Background operators:
% 32.15/22.48  
% 32.15/22.48  
% 32.15/22.48  %Foreground operators:
% 32.15/22.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.15/22.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 32.15/22.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 32.15/22.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.15/22.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 32.15/22.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 32.15/22.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 32.15/22.48  tff('#skF_2', type, '#skF_2': $i).
% 32.15/22.48  tff('#skF_3', type, '#skF_3': $i).
% 32.15/22.48  tff('#skF_1', type, '#skF_1': $i).
% 32.15/22.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 32.15/22.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 32.15/22.48  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 32.15/22.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 32.15/22.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 32.15/22.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.15/22.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.15/22.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 32.15/22.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 32.15/22.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 32.15/22.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 32.15/22.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 32.15/22.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 32.15/22.48  
% 32.30/22.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 32.30/22.50  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 32.30/22.50  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 32.30/22.50  tff(f_108, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tops_2)).
% 32.30/22.50  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 32.30/22.50  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 32.30/22.50  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 32.30/22.50  tff(f_95, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_tops_2)).
% 32.30/22.50  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tops_2)).
% 32.30/22.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 32.30/22.50  tff(c_32, plain, (![A_44, B_45]: (m1_subset_1(A_44, k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_67])).
% 32.30/22.50  tff(c_132, plain, (![A_85, B_86, C_87]: (k9_subset_1(A_85, B_86, C_87)=k3_xboole_0(B_86, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 32.30/22.50  tff(c_170, plain, (![B_94, B_95, A_96]: (k9_subset_1(B_94, B_95, A_96)=k3_xboole_0(B_95, A_96) | ~r1_tarski(A_96, B_94))), inference(resolution, [status(thm)], [c_32, c_132])).
% 32.30/22.50  tff(c_187, plain, (![B_2, B_95]: (k9_subset_1(B_2, B_95, B_2)=k3_xboole_0(B_95, B_2))), inference(resolution, [status(thm)], [c_6, c_170])).
% 32.30/22.50  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 32.30/22.50  tff(c_141, plain, (![B_86]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_86, '#skF_2')=k3_xboole_0(B_86, '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_132])).
% 32.30/22.50  tff(c_280, plain, (![A_108, C_109, B_110]: (k9_subset_1(A_108, C_109, B_110)=k9_subset_1(A_108, B_110, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.30/22.50  tff(c_292, plain, (![B_110]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_110, '#skF_2')=k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', B_110))), inference(resolution, [status(thm)], [c_46, c_280])).
% 32.30/22.50  tff(c_352, plain, (![B_112]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', B_112)=k3_xboole_0(B_112, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_292])).
% 32.30/22.50  tff(c_377, plain, (k3_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2')=k3_xboole_0('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_187, c_352])).
% 32.30/22.50  tff(c_215, plain, (![A_101, B_102, C_103]: (m1_subset_1(k9_subset_1(A_101, B_102, C_103), k1_zfmisc_1(A_101)) | ~m1_subset_1(C_103, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 32.30/22.50  tff(c_30, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 32.30/22.50  tff(c_393, plain, (![A_113, B_114, C_115]: (r1_tarski(k9_subset_1(A_113, B_114, C_115), A_113) | ~m1_subset_1(C_115, k1_zfmisc_1(A_113)))), inference(resolution, [status(thm)], [c_215, c_30])).
% 32.30/22.50  tff(c_410, plain, (![B_95, B_2]: (r1_tarski(k3_xboole_0(B_95, B_2), B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_393])).
% 32.30/22.50  tff(c_517, plain, (r1_tarski(k3_xboole_0('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_377, c_410])).
% 32.30/22.50  tff(c_1034, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_517])).
% 32.30/22.50  tff(c_1042, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_1034])).
% 32.30/22.50  tff(c_1046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1042])).
% 32.30/22.50  tff(c_1048, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_517])).
% 32.30/22.50  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 32.30/22.50  tff(c_34, plain, (![A_46]: (l1_struct_0(A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 32.30/22.50  tff(c_42, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 32.30/22.50  tff(c_231, plain, (![A_101, B_102, C_103]: (r1_tarski(k9_subset_1(A_101, B_102, C_103), A_101) | ~m1_subset_1(C_103, k1_zfmisc_1(A_101)))), inference(resolution, [status(thm)], [c_215, c_30])).
% 32.30/22.50  tff(c_918, plain, (![C_154, A_155, B_156]: (m1_subset_1(C_154, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155)))) | ~r1_tarski(C_154, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155)))) | ~l1_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_95])).
% 32.30/22.50  tff(c_953, plain, (![A_101, B_102, C_103, A_155]: (m1_subset_1(k9_subset_1(A_101, B_102, C_103), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155)))) | ~m1_subset_1(A_101, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155)))) | ~l1_struct_0(A_155) | ~m1_subset_1(C_103, k1_zfmisc_1(A_101)))), inference(resolution, [status(thm)], [c_231, c_918])).
% 32.30/22.50  tff(c_1135, plain, (![B_164, A_165, C_166]: (v2_tops_2(B_164, A_165) | ~v2_tops_2(C_166, A_165) | ~r1_tarski(B_164, C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_165)))) | ~m1_subset_1(B_164, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_165)))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_85])).
% 32.30/22.50  tff(c_6040, plain, (![A_302, B_303, C_304, A_305]: (v2_tops_2(k9_subset_1(A_302, B_303, C_304), A_305) | ~v2_tops_2(A_302, A_305) | ~m1_subset_1(A_302, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_305)))) | ~m1_subset_1(k9_subset_1(A_302, B_303, C_304), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_305)))) | ~l1_pre_topc(A_305) | ~m1_subset_1(C_304, k1_zfmisc_1(A_302)))), inference(resolution, [status(thm)], [c_231, c_1135])).
% 32.30/22.50  tff(c_77818, plain, (![A_1210, B_1211, C_1212, A_1213]: (v2_tops_2(k9_subset_1(A_1210, B_1211, C_1212), A_1213) | ~v2_tops_2(A_1210, A_1213) | ~l1_pre_topc(A_1213) | ~m1_subset_1(A_1210, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1213)))) | ~l1_struct_0(A_1213) | ~m1_subset_1(C_1212, k1_zfmisc_1(A_1210)))), inference(resolution, [status(thm)], [c_953, c_6040])).
% 32.30/22.50  tff(c_77893, plain, (![B_1211, C_1212]: (v2_tops_2(k9_subset_1('#skF_2', B_1211, C_1212), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_struct_0('#skF_1') | ~m1_subset_1(C_1212, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_46, c_77818])).
% 32.30/22.50  tff(c_77966, plain, (![B_1211, C_1212]: (v2_tops_2(k9_subset_1('#skF_2', B_1211, C_1212), '#skF_1') | ~l1_struct_0('#skF_1') | ~m1_subset_1(C_1212, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_77893])).
% 32.30/22.50  tff(c_77967, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_77966])).
% 32.30/22.50  tff(c_77970, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_77967])).
% 32.30/22.50  tff(c_77974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_77970])).
% 32.30/22.50  tff(c_77980, plain, (![B_1214, C_1215]: (v2_tops_2(k9_subset_1('#skF_2', B_1214, C_1215), '#skF_1') | ~m1_subset_1(C_1215, k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_77966])).
% 32.30/22.50  tff(c_78048, plain, (![B_95]: (v2_tops_2(k3_xboole_0(B_95, '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_187, c_77980])).
% 32.30/22.50  tff(c_78056, plain, (![B_95]: (v2_tops_2(k3_xboole_0(B_95, '#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_78048])).
% 32.30/22.50  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 32.30/22.50  tff(c_140, plain, (![B_86]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_86, '#skF_3')=k3_xboole_0(B_86, '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_132])).
% 32.30/22.50  tff(c_290, plain, (![B_110]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_110, '#skF_3')=k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3', B_110))), inference(resolution, [status(thm)], [c_44, c_280])).
% 32.30/22.50  tff(c_301, plain, (![B_111]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_3', B_111)=k3_xboole_0(B_111, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_290])).
% 32.30/22.50  tff(c_315, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_301, c_141])).
% 32.30/22.50  tff(c_40, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 32.30/22.50  tff(c_142, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_40])).
% 32.30/22.50  tff(c_340, plain, (~v2_tops_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_142])).
% 32.30/22.50  tff(c_78059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78056, c_340])).
% 32.30/22.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.30/22.50  
% 32.30/22.50  Inference rules
% 32.30/22.50  ----------------------
% 32.30/22.50  #Ref     : 0
% 32.30/22.50  #Sup     : 19932
% 32.30/22.50  #Fact    : 0
% 32.30/22.50  #Define  : 0
% 32.30/22.50  #Split   : 11
% 32.30/22.50  #Chain   : 0
% 32.30/22.50  #Close   : 0
% 32.30/22.50  
% 32.30/22.50  Ordering : KBO
% 32.30/22.50  
% 32.30/22.50  Simplification rules
% 32.30/22.50  ----------------------
% 32.30/22.50  #Subsume      : 1053
% 32.30/22.50  #Demod        : 8644
% 32.30/22.50  #Tautology    : 4353
% 32.30/22.50  #SimpNegUnit  : 0
% 32.30/22.50  #BackRed      : 14
% 32.30/22.50  
% 32.30/22.50  #Partial instantiations: 0
% 32.30/22.50  #Strategies tried      : 1
% 32.30/22.50  
% 32.30/22.50  Timing (in seconds)
% 32.30/22.50  ----------------------
% 32.30/22.50  Preprocessing        : 0.34
% 32.30/22.50  Parsing              : 0.18
% 32.30/22.50  CNF conversion       : 0.02
% 32.30/22.50  Main loop            : 21.39
% 32.30/22.50  Inferencing          : 2.31
% 32.30/22.50  Reduction            : 11.57
% 32.30/22.50  Demodulation         : 10.46
% 32.30/22.50  BG Simplification    : 0.35
% 32.30/22.50  Subsumption          : 5.94
% 32.30/22.50  Abstraction          : 0.49
% 32.30/22.50  MUC search           : 0.00
% 32.30/22.50  Cooper               : 0.00
% 32.30/22.50  Total                : 21.77
% 32.30/22.50  Index Insertion      : 0.00
% 32.30/22.50  Index Deletion       : 0.00
% 32.30/22.50  Index Matching       : 0.00
% 32.30/22.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
