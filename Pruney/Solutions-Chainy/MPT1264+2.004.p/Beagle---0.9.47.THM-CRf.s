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
% DateTime   : Thu Dec  3 10:21:38 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 236 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 518 expanded)
%              Number of equality atoms :   40 ( 143 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_18,c_40])).

tff(c_82,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_78])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_84,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_34])).

tff(c_192,plain,(
    ! [A_48,B_49,C_50] :
      ( k9_subset_1(A_48,B_49,C_50) = k3_xboole_0(B_49,C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_201,plain,(
    ! [B_49] : k9_subset_1(k2_struct_0('#skF_1'),B_49,'#skF_2') = k3_xboole_0(B_49,'#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_192])).

tff(c_26,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_83,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_26])).

tff(c_212,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_83])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_85,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_30])).

tff(c_90,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_85,c_90])).

tff(c_114,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_97,c_114])).

tff(c_32,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_349,plain,(
    ! [A_70,B_71] :
      ( k2_pre_topc(A_70,B_71) = k2_struct_0(A_70)
      | ~ v1_tops_1(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_356,plain,(
    ! [B_71] :
      ( k2_pre_topc('#skF_1',B_71) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_71,'#skF_1')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_349])).

tff(c_360,plain,(
    ! [B_72] :
      ( k2_pre_topc('#skF_1',B_72) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_72,'#skF_1')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_356])).

tff(c_370,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_360])).

tff(c_377,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_370])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_136,plain,(
    ! [B_44,A_45] : k1_setfam_1(k2_tarski(B_44,A_45)) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_99])).

tff(c_10,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_142,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_10])).

tff(c_28,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_200,plain,(
    ! [B_49] : k9_subset_1(k2_struct_0('#skF_1'),B_49,'#skF_3') = k3_xboole_0(B_49,'#skF_3') ),
    inference(resolution,[status(thm)],[c_85,c_192])).

tff(c_231,plain,(
    ! [A_56,C_57,B_58] :
      ( k9_subset_1(A_56,C_57,B_58) = k9_subset_1(A_56,B_58,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_235,plain,(
    ! [B_58] : k9_subset_1(k2_struct_0('#skF_1'),B_58,'#skF_3') = k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_58) ),
    inference(resolution,[status(thm)],[c_85,c_231])).

tff(c_240,plain,(
    ! [B_58] : k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_58) = k3_xboole_0(B_58,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_235])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_378,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_pre_topc(A_73,k9_subset_1(u1_struct_0(A_73),B_74,k2_pre_topc(A_73,C_75))) = k2_pre_topc(A_73,k9_subset_1(u1_struct_0(A_73),B_74,C_75))
      | ~ v3_pre_topc(B_74,A_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_393,plain,(
    ! [B_74,C_75] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_74,k2_pre_topc('#skF_1',C_75))) = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_74,C_75))
      | ~ v3_pre_topc(B_74,'#skF_1')
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_378])).

tff(c_425,plain,(
    ! [B_79,C_80] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_79,k2_pre_topc('#skF_1',C_80))) = k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_79,C_80))
      | ~ v3_pre_topc(B_79,'#skF_1')
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_82,c_82,c_82,c_393])).

tff(c_455,plain,(
    ! [C_80] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',C_80)) = k2_pre_topc('#skF_1',k3_xboole_0(k2_pre_topc('#skF_1',C_80),'#skF_3'))
      | ~ v3_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_425])).

tff(c_468,plain,(
    ! [C_81] :
      ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_3',k2_pre_topc('#skF_1',C_81))) = k2_pre_topc('#skF_1',k3_xboole_0(C_81,'#skF_3'))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_28,c_240,c_142,c_455])).

tff(c_478,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_84,c_468])).

tff(c_482,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_377,c_142,c_478])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_482])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.39  
% 2.74/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.40  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.40  
% 2.74/1.40  %Foreground sorts:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Background operators:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Foreground operators:
% 2.74/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.74/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.40  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.74/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.74/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.40  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.74/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.74/1.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.74/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.74/1.40  
% 2.74/1.41  tff(f_93, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 2.74/1.41  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.74/1.41  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.74/1.41  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.74/1.41  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.74/1.41  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.74/1.41  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 2.74/1.41  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.74/1.41  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.74/1.41  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.74/1.41  tff(f_76, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 2.74/1.41  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.41  tff(c_18, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.41  tff(c_40, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.74/1.41  tff(c_78, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_18, c_40])).
% 2.74/1.41  tff(c_82, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_78])).
% 2.74/1.41  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.41  tff(c_84, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_34])).
% 2.74/1.41  tff(c_192, plain, (![A_48, B_49, C_50]: (k9_subset_1(A_48, B_49, C_50)=k3_xboole_0(B_49, C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.41  tff(c_201, plain, (![B_49]: (k9_subset_1(k2_struct_0('#skF_1'), B_49, '#skF_2')=k3_xboole_0(B_49, '#skF_2'))), inference(resolution, [status(thm)], [c_84, c_192])).
% 2.74/1.41  tff(c_26, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.41  tff(c_83, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_26])).
% 2.74/1.41  tff(c_212, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_83])).
% 2.74/1.41  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.41  tff(c_85, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_30])).
% 2.74/1.41  tff(c_90, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.74/1.41  tff(c_97, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_85, c_90])).
% 2.74/1.41  tff(c_114, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.74/1.41  tff(c_122, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_97, c_114])).
% 2.74/1.41  tff(c_32, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.41  tff(c_349, plain, (![A_70, B_71]: (k2_pre_topc(A_70, B_71)=k2_struct_0(A_70) | ~v1_tops_1(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.74/1.41  tff(c_356, plain, (![B_71]: (k2_pre_topc('#skF_1', B_71)=k2_struct_0('#skF_1') | ~v1_tops_1(B_71, '#skF_1') | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_349])).
% 2.74/1.41  tff(c_360, plain, (![B_72]: (k2_pre_topc('#skF_1', B_72)=k2_struct_0('#skF_1') | ~v1_tops_1(B_72, '#skF_1') | ~m1_subset_1(B_72, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_356])).
% 2.74/1.41  tff(c_370, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_360])).
% 2.74/1.41  tff(c_377, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_370])).
% 2.74/1.41  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.41  tff(c_99, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.41  tff(c_136, plain, (![B_44, A_45]: (k1_setfam_1(k2_tarski(B_44, A_45))=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_4, c_99])).
% 2.74/1.41  tff(c_10, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.41  tff(c_142, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_136, c_10])).
% 2.74/1.41  tff(c_28, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.41  tff(c_200, plain, (![B_49]: (k9_subset_1(k2_struct_0('#skF_1'), B_49, '#skF_3')=k3_xboole_0(B_49, '#skF_3'))), inference(resolution, [status(thm)], [c_85, c_192])).
% 2.74/1.41  tff(c_231, plain, (![A_56, C_57, B_58]: (k9_subset_1(A_56, C_57, B_58)=k9_subset_1(A_56, B_58, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.41  tff(c_235, plain, (![B_58]: (k9_subset_1(k2_struct_0('#skF_1'), B_58, '#skF_3')=k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_58))), inference(resolution, [status(thm)], [c_85, c_231])).
% 2.74/1.41  tff(c_240, plain, (![B_58]: (k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_58)=k3_xboole_0(B_58, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_235])).
% 2.74/1.41  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.74/1.41  tff(c_378, plain, (![A_73, B_74, C_75]: (k2_pre_topc(A_73, k9_subset_1(u1_struct_0(A_73), B_74, k2_pre_topc(A_73, C_75)))=k2_pre_topc(A_73, k9_subset_1(u1_struct_0(A_73), B_74, C_75)) | ~v3_pre_topc(B_74, A_73) | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.74/1.41  tff(c_393, plain, (![B_74, C_75]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_74, k2_pre_topc('#skF_1', C_75)))=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_74, C_75)) | ~v3_pre_topc(B_74, '#skF_1') | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_378])).
% 2.74/1.41  tff(c_425, plain, (![B_79, C_80]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_79, k2_pre_topc('#skF_1', C_80)))=k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_79, C_80)) | ~v3_pre_topc(B_79, '#skF_1') | ~m1_subset_1(C_80, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_82, c_82, c_82, c_393])).
% 2.74/1.41  tff(c_455, plain, (![C_80]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', C_80))=k2_pre_topc('#skF_1', k3_xboole_0(k2_pre_topc('#skF_1', C_80), '#skF_3')) | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(C_80, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_240, c_425])).
% 2.74/1.41  tff(c_468, plain, (![C_81]: (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', k2_pre_topc('#skF_1', C_81)))=k2_pre_topc('#skF_1', k3_xboole_0(C_81, '#skF_3')) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_28, c_240, c_142, c_455])).
% 2.74/1.41  tff(c_478, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_84, c_468])).
% 2.74/1.41  tff(c_482, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_377, c_142, c_478])).
% 2.74/1.41  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_482])).
% 2.74/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  Inference rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Ref     : 0
% 2.74/1.41  #Sup     : 101
% 2.74/1.41  #Fact    : 0
% 2.74/1.41  #Define  : 0
% 2.74/1.41  #Split   : 1
% 2.74/1.41  #Chain   : 0
% 2.74/1.41  #Close   : 0
% 2.74/1.41  
% 2.74/1.41  Ordering : KBO
% 2.74/1.41  
% 2.74/1.41  Simplification rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Subsume      : 9
% 2.74/1.41  #Demod        : 66
% 2.74/1.41  #Tautology    : 55
% 2.74/1.41  #SimpNegUnit  : 3
% 2.74/1.41  #BackRed      : 4
% 2.74/1.41  
% 2.74/1.41  #Partial instantiations: 0
% 2.74/1.41  #Strategies tried      : 1
% 2.74/1.41  
% 2.74/1.41  Timing (in seconds)
% 2.74/1.41  ----------------------
% 2.74/1.41  Preprocessing        : 0.31
% 2.74/1.41  Parsing              : 0.17
% 2.74/1.42  CNF conversion       : 0.02
% 2.74/1.42  Main loop            : 0.28
% 2.74/1.42  Inferencing          : 0.10
% 2.74/1.42  Reduction            : 0.10
% 2.74/1.42  Demodulation         : 0.08
% 2.74/1.42  BG Simplification    : 0.02
% 2.74/1.42  Subsumption          : 0.04
% 2.74/1.42  Abstraction          : 0.02
% 2.74/1.42  MUC search           : 0.00
% 2.74/1.42  Cooper               : 0.00
% 2.74/1.42  Total                : 0.63
% 2.74/1.42  Index Insertion      : 0.00
% 2.74/1.42  Index Deletion       : 0.00
% 2.74/1.42  Index Matching       : 0.00
% 2.74/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
