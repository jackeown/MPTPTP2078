%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:40 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 189 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  108 ( 425 expanded)
%              Number of equality atoms :   30 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_94,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_20,c_42])).

tff(c_51,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_53,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_36])).

tff(c_124,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,C_53) = k3_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_133,plain,(
    ! [B_52] : k9_subset_1(k2_struct_0('#skF_2'),B_52,'#skF_3') = k3_xboole_0(B_52,'#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_124])).

tff(c_28,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).

tff(c_143,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_52])).

tff(c_30,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_32])).

tff(c_70,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_70])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_86,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_81,c_8])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_1'(A_44,B_45),B_45)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_153,plain,(
    ! [B_56,B_57,A_58] :
      ( k9_subset_1(B_56,B_57,A_58) = k3_xboole_0(B_57,A_58)
      | ~ r1_tarski(A_58,B_56) ) ),
    inference(resolution,[status(thm)],[c_16,c_124])).

tff(c_160,plain,(
    ! [A_1,B_57] : k9_subset_1(A_1,B_57,A_1) = k3_xboole_0(B_57,A_1) ),
    inference(resolution,[status(thm)],[c_105,c_153])).

tff(c_34,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_193,plain,(
    ! [A_68,B_69] :
      ( k2_pre_topc(A_68,B_69) = k2_struct_0(A_68)
      | ~ v1_tops_1(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_200,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_2',B_69) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_69,'#skF_2')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_193])).

tff(c_420,plain,(
    ! [B_82] :
      ( k2_pre_topc('#skF_2',B_82) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_82,'#skF_2')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_200])).

tff(c_430,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_420])).

tff(c_435,plain,(
    k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_430])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_502,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_pre_topc(A_88,k9_subset_1(u1_struct_0(A_88),B_89,k2_pre_topc(A_88,C_90))) = k2_pre_topc(A_88,k9_subset_1(u1_struct_0(A_88),B_89,C_90))
      | ~ v3_pre_topc(B_89,A_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_520,plain,(
    ! [B_89,C_90] :
      ( k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_89,k2_pre_topc('#skF_2',C_90))) = k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_89,C_90))
      | ~ v3_pre_topc(B_89,'#skF_2')
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_502])).

tff(c_561,plain,(
    ! [B_93,C_94] :
      ( k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_93,k2_pre_topc('#skF_2',C_94))) = k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_93,C_94))
      | ~ v3_pre_topc(B_93,'#skF_2')
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_51,c_51,c_51,c_520])).

tff(c_583,plain,(
    ! [B_93] :
      ( k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_93,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_93,'#skF_3'))
      | ~ v3_pre_topc(B_93,'#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_561])).

tff(c_864,plain,(
    ! [B_134] :
      ( k2_pre_topc('#skF_2',k3_xboole_0(B_134,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0(B_134,'#skF_3'))
      | ~ v3_pre_topc(B_134,'#skF_2')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_160,c_133,c_583])).

tff(c_871,plain,
    ( k2_pre_topc('#skF_2',k3_xboole_0('#skF_4',k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3'))
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_864])).

tff(c_878,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_86,c_871])).

tff(c_880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_878])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.49  
% 3.22/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.49  %$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.22/1.49  
% 3.22/1.49  %Foreground sorts:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Background operators:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Foreground operators:
% 3.22/1.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.22/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.49  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.22/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.22/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.22/1.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.22/1.49  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.22/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.22/1.49  
% 3.22/1.50  tff(f_94, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 3.22/1.50  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.22/1.50  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.22/1.50  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.22/1.50  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.22/1.50  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.22/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.22/1.50  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.22/1.50  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 3.22/1.50  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.22/1.50  tff(c_20, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.22/1.50  tff(c_42, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.50  tff(c_47, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_20, c_42])).
% 3.22/1.50  tff(c_51, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_47])).
% 3.22/1.50  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.22/1.50  tff(c_53, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_36])).
% 3.22/1.50  tff(c_124, plain, (![A_51, B_52, C_53]: (k9_subset_1(A_51, B_52, C_53)=k3_xboole_0(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.22/1.50  tff(c_133, plain, (![B_52]: (k9_subset_1(k2_struct_0('#skF_2'), B_52, '#skF_3')=k3_xboole_0(B_52, '#skF_3'))), inference(resolution, [status(thm)], [c_53, c_124])).
% 3.22/1.50  tff(c_28, plain, (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.22/1.50  tff(c_52, plain, (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_28])).
% 3.22/1.50  tff(c_143, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_52])).
% 3.22/1.50  tff(c_30, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.22/1.50  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.22/1.50  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_32])).
% 3.22/1.50  tff(c_70, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.50  tff(c_81, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_70])).
% 3.22/1.50  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.22/1.50  tff(c_86, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_81, c_8])).
% 3.22/1.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.22/1.50  tff(c_100, plain, (![A_44, B_45]: (~r2_hidden('#skF_1'(A_44, B_45), B_45) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.22/1.50  tff(c_105, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_100])).
% 3.22/1.50  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.50  tff(c_153, plain, (![B_56, B_57, A_58]: (k9_subset_1(B_56, B_57, A_58)=k3_xboole_0(B_57, A_58) | ~r1_tarski(A_58, B_56))), inference(resolution, [status(thm)], [c_16, c_124])).
% 3.22/1.50  tff(c_160, plain, (![A_1, B_57]: (k9_subset_1(A_1, B_57, A_1)=k3_xboole_0(B_57, A_1))), inference(resolution, [status(thm)], [c_105, c_153])).
% 3.22/1.50  tff(c_34, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.22/1.50  tff(c_193, plain, (![A_68, B_69]: (k2_pre_topc(A_68, B_69)=k2_struct_0(A_68) | ~v1_tops_1(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.22/1.50  tff(c_200, plain, (![B_69]: (k2_pre_topc('#skF_2', B_69)=k2_struct_0('#skF_2') | ~v1_tops_1(B_69, '#skF_2') | ~m1_subset_1(B_69, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_193])).
% 3.22/1.50  tff(c_420, plain, (![B_82]: (k2_pre_topc('#skF_2', B_82)=k2_struct_0('#skF_2') | ~v1_tops_1(B_82, '#skF_2') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_200])).
% 3.22/1.50  tff(c_430, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_420])).
% 3.22/1.50  tff(c_435, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_430])).
% 3.22/1.50  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.22/1.50  tff(c_502, plain, (![A_88, B_89, C_90]: (k2_pre_topc(A_88, k9_subset_1(u1_struct_0(A_88), B_89, k2_pre_topc(A_88, C_90)))=k2_pre_topc(A_88, k9_subset_1(u1_struct_0(A_88), B_89, C_90)) | ~v3_pre_topc(B_89, A_88) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.22/1.50  tff(c_520, plain, (![B_89, C_90]: (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_89, k2_pre_topc('#skF_2', C_90)))=k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_89, C_90)) | ~v3_pre_topc(B_89, '#skF_2') | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_502])).
% 3.22/1.50  tff(c_561, plain, (![B_93, C_94]: (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_93, k2_pre_topc('#skF_2', C_94)))=k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_93, C_94)) | ~v3_pre_topc(B_93, '#skF_2') | ~m1_subset_1(C_94, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_51, c_51, c_51, c_520])).
% 3.22/1.50  tff(c_583, plain, (![B_93]: (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_93, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_93, '#skF_3')) | ~v3_pre_topc(B_93, '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_435, c_561])).
% 3.22/1.50  tff(c_864, plain, (![B_134]: (k2_pre_topc('#skF_2', k3_xboole_0(B_134, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0(B_134, '#skF_3')) | ~v3_pre_topc(B_134, '#skF_2') | ~m1_subset_1(B_134, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_160, c_133, c_583])).
% 3.22/1.50  tff(c_871, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3')) | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_864])).
% 3.22/1.50  tff(c_878, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_86, c_871])).
% 3.22/1.50  tff(c_880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_878])).
% 3.22/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  Inference rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Ref     : 0
% 3.22/1.50  #Sup     : 186
% 3.22/1.50  #Fact    : 0
% 3.22/1.50  #Define  : 0
% 3.22/1.50  #Split   : 5
% 3.22/1.50  #Chain   : 0
% 3.22/1.50  #Close   : 0
% 3.22/1.50  
% 3.22/1.50  Ordering : KBO
% 3.22/1.50  
% 3.22/1.50  Simplification rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Subsume      : 40
% 3.22/1.50  #Demod        : 149
% 3.22/1.50  #Tautology    : 72
% 3.22/1.51  #SimpNegUnit  : 11
% 3.22/1.51  #BackRed      : 4
% 3.22/1.51  
% 3.22/1.51  #Partial instantiations: 0
% 3.22/1.51  #Strategies tried      : 1
% 3.22/1.51  
% 3.22/1.51  Timing (in seconds)
% 3.22/1.51  ----------------------
% 3.22/1.51  Preprocessing        : 0.32
% 3.22/1.51  Parsing              : 0.17
% 3.22/1.51  CNF conversion       : 0.02
% 3.22/1.51  Main loop            : 0.42
% 3.22/1.51  Inferencing          : 0.15
% 3.22/1.51  Reduction            : 0.13
% 3.22/1.51  Demodulation         : 0.09
% 3.22/1.51  BG Simplification    : 0.02
% 3.22/1.51  Subsumption          : 0.08
% 3.22/1.51  Abstraction          : 0.03
% 3.22/1.51  MUC search           : 0.00
% 3.22/1.51  Cooper               : 0.00
% 3.22/1.51  Total                : 0.78
% 3.22/1.51  Index Insertion      : 0.00
% 3.22/1.51  Index Deletion       : 0.00
% 3.22/1.51  Index Matching       : 0.00
% 3.22/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
