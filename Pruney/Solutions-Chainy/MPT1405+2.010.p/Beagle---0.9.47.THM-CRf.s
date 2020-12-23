%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:31 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 138 expanded)
%              Number of leaves         :   34 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 266 expanded)
%              Number of equality atoms :    9 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_36,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_45,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_95,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | v1_xboole_0(B_42)
      | ~ m1_subset_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_115,plain,(
    ! [A_45,A_46] :
      ( r1_tarski(A_45,A_46)
      | v1_xboole_0(k1_zfmisc_1(A_46))
      | ~ m1_subset_1(A_45,k1_zfmisc_1(A_46)) ) ),
    inference(resolution,[status(thm)],[c_95,c_8])).

tff(c_124,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,A_47)
      | v1_xboole_0(k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_45,c_115])).

tff(c_79,plain,(
    ! [C_35,A_36] :
      ( r2_hidden(C_35,k1_zfmisc_1(A_36))
      | ~ r1_tarski(C_35,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_36,C_35] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_36))
      | ~ r1_tarski(C_35,A_36) ) ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_128,plain,(
    ! [C_48,A_49] :
      ( ~ r1_tarski(C_48,A_49)
      | r1_tarski(A_49,A_49) ) ),
    inference(resolution,[status(thm)],[c_124,c_83])).

tff(c_137,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_73,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_69])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_38])).

tff(c_122,plain,
    ( r1_tarski('#skF_5',k2_struct_0('#skF_4'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_74,c_115])).

tff(c_151,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_155,plain,(
    ! [C_53] : ~ r1_tarski(C_53,k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_151,c_83])).

tff(c_172,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_137,c_155])).

tff(c_173,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_42,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    ! [A_17] :
      ( k1_tops_1(A_17,k2_struct_0(A_17)) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_243,plain,(
    ! [C_74,A_75,B_76] :
      ( m2_connsp_2(C_74,A_75,B_76)
      | ~ r1_tarski(B_76,k1_tops_1(A_75,C_74))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_405,plain,(
    ! [A_94,B_95] :
      ( m2_connsp_2(k2_struct_0(A_94),A_94,B_95)
      | ~ r1_tarski(B_95,k2_struct_0(A_94))
      | ~ m1_subset_1(k2_struct_0(A_94),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_243])).

tff(c_407,plain,(
    ! [B_95] :
      ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4',B_95)
      | ~ r1_tarski(B_95,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_405])).

tff(c_410,plain,(
    ! [B_96] :
      ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4',B_96)
      | ~ r1_tarski(B_96,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_42,c_40,c_73,c_45,c_407])).

tff(c_413,plain,
    ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5')
    | ~ r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_410])).

tff(c_420,plain,(
    m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_413])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:27:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.33  
% 2.76/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.34  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.76/1.34  
% 2.76/1.34  %Foreground sorts:
% 2.76/1.34  
% 2.76/1.34  
% 2.76/1.34  %Background operators:
% 2.76/1.34  
% 2.76/1.34  
% 2.76/1.34  %Foreground operators:
% 2.76/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.76/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.76/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.76/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.76/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.76/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.76/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.76/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.34  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.76/1.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.76/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.34  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.76/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.34  
% 2.88/1.35  tff(f_91, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.88/1.35  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.88/1.35  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.88/1.35  tff(f_44, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.88/1.35  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.88/1.35  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.88/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.88/1.35  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.88/1.35  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.88/1.35  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.88/1.35  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.88/1.35  tff(c_36, plain, (~m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.35  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.88/1.35  tff(c_20, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.88/1.35  tff(c_22, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.88/1.35  tff(c_45, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.88/1.35  tff(c_95, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | v1_xboole_0(B_42) | ~m1_subset_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.88/1.35  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.35  tff(c_115, plain, (![A_45, A_46]: (r1_tarski(A_45, A_46) | v1_xboole_0(k1_zfmisc_1(A_46)) | ~m1_subset_1(A_45, k1_zfmisc_1(A_46)))), inference(resolution, [status(thm)], [c_95, c_8])).
% 2.88/1.35  tff(c_124, plain, (![A_47]: (r1_tarski(A_47, A_47) | v1_xboole_0(k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_45, c_115])).
% 2.88/1.35  tff(c_79, plain, (![C_35, A_36]: (r2_hidden(C_35, k1_zfmisc_1(A_36)) | ~r1_tarski(C_35, A_36))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.35  tff(c_83, plain, (![A_36, C_35]: (~v1_xboole_0(k1_zfmisc_1(A_36)) | ~r1_tarski(C_35, A_36))), inference(resolution, [status(thm)], [c_79, c_2])).
% 2.88/1.35  tff(c_128, plain, (![C_48, A_49]: (~r1_tarski(C_48, A_49) | r1_tarski(A_49, A_49))), inference(resolution, [status(thm)], [c_124, c_83])).
% 2.88/1.35  tff(c_137, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_6, c_128])).
% 2.88/1.35  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.35  tff(c_28, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.88/1.35  tff(c_64, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.88/1.35  tff(c_69, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_28, c_64])).
% 2.88/1.35  tff(c_73, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_69])).
% 2.88/1.35  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.35  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_38])).
% 2.88/1.35  tff(c_122, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_74, c_115])).
% 2.88/1.35  tff(c_151, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_122])).
% 2.88/1.35  tff(c_155, plain, (![C_53]: (~r1_tarski(C_53, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_151, c_83])).
% 2.88/1.35  tff(c_172, plain, $false, inference(resolution, [status(thm)], [c_137, c_155])).
% 2.88/1.35  tff(c_173, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_122])).
% 2.88/1.35  tff(c_42, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.35  tff(c_30, plain, (![A_17]: (k1_tops_1(A_17, k2_struct_0(A_17))=k2_struct_0(A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.88/1.35  tff(c_243, plain, (![C_74, A_75, B_76]: (m2_connsp_2(C_74, A_75, B_76) | ~r1_tarski(B_76, k1_tops_1(A_75, C_74)) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.88/1.35  tff(c_405, plain, (![A_94, B_95]: (m2_connsp_2(k2_struct_0(A_94), A_94, B_95) | ~r1_tarski(B_95, k2_struct_0(A_94)) | ~m1_subset_1(k2_struct_0(A_94), k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(superposition, [status(thm), theory('equality')], [c_30, c_243])).
% 2.88/1.35  tff(c_407, plain, (![B_95]: (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', B_95) | ~r1_tarski(B_95, k2_struct_0('#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_405])).
% 2.88/1.35  tff(c_410, plain, (![B_96]: (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', B_96) | ~r1_tarski(B_96, k2_struct_0('#skF_4')) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_42, c_40, c_73, c_45, c_407])).
% 2.88/1.35  tff(c_413, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5') | ~r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_74, c_410])).
% 2.88/1.35  tff(c_420, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_413])).
% 2.88/1.35  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_420])).
% 2.88/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.35  
% 2.88/1.35  Inference rules
% 2.88/1.35  ----------------------
% 2.88/1.35  #Ref     : 0
% 2.88/1.35  #Sup     : 77
% 2.88/1.35  #Fact    : 0
% 2.88/1.35  #Define  : 0
% 2.88/1.35  #Split   : 4
% 2.88/1.35  #Chain   : 0
% 2.88/1.35  #Close   : 0
% 2.88/1.35  
% 2.88/1.35  Ordering : KBO
% 2.88/1.35  
% 2.88/1.35  Simplification rules
% 2.88/1.35  ----------------------
% 2.88/1.35  #Subsume      : 7
% 2.88/1.35  #Demod        : 45
% 2.88/1.35  #Tautology    : 19
% 2.88/1.35  #SimpNegUnit  : 1
% 2.88/1.35  #BackRed      : 1
% 2.88/1.35  
% 2.88/1.35  #Partial instantiations: 0
% 2.88/1.35  #Strategies tried      : 1
% 2.88/1.35  
% 2.88/1.35  Timing (in seconds)
% 2.88/1.35  ----------------------
% 2.88/1.35  Preprocessing        : 0.32
% 2.88/1.36  Parsing              : 0.17
% 2.88/1.36  CNF conversion       : 0.02
% 2.88/1.36  Main loop            : 0.29
% 2.88/1.36  Inferencing          : 0.11
% 2.88/1.36  Reduction            : 0.08
% 2.88/1.36  Demodulation         : 0.06
% 2.88/1.36  BG Simplification    : 0.02
% 2.88/1.36  Subsumption          : 0.06
% 2.88/1.36  Abstraction          : 0.02
% 2.88/1.36  MUC search           : 0.00
% 2.88/1.36  Cooper               : 0.00
% 2.88/1.36  Total                : 0.64
% 2.88/1.36  Index Insertion      : 0.00
% 2.88/1.36  Index Deletion       : 0.00
% 2.88/1.36  Index Matching       : 0.00
% 2.88/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
