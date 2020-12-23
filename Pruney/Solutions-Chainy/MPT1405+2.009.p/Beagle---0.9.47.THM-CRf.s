%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:31 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 140 expanded)
%              Number of leaves         :   36 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 266 expanded)
%              Number of equality atoms :    9 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_38,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_106,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(A_47,B_48)
      | v1_xboole_0(B_48)
      | ~ m1_subset_1(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_126,plain,(
    ! [A_51,A_52] :
      ( r1_tarski(A_51,A_52)
      | v1_xboole_0(k1_zfmisc_1(A_52))
      | ~ m1_subset_1(A_51,k1_zfmisc_1(A_52)) ) ),
    inference(resolution,[status(thm)],[c_106,c_8])).

tff(c_135,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,A_53)
      | v1_xboole_0(k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_47,c_126])).

tff(c_87,plain,(
    ! [C_41,A_42] :
      ( r2_hidden(C_41,k1_zfmisc_1(A_42))
      | ~ r1_tarski(C_41,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_42,C_41] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_42))
      | ~ r1_tarski(C_41,A_42) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_139,plain,(
    ! [C_54,A_55] :
      ( ~ r1_tarski(C_54,A_55)
      | r1_tarski(A_55,A_55) ) ),
    inference(resolution,[status(thm)],[c_135,c_95])).

tff(c_148,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_6,c_139])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_75,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_71])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_40])).

tff(c_133,plain,
    ( r1_tarski('#skF_5',k2_struct_0('#skF_4'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_76,c_126])).

tff(c_162,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_166,plain,(
    ! [C_59] : ~ r1_tarski(C_59,k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_162,c_95])).

tff(c_178,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_148,c_166])).

tff(c_179,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_44,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    ! [A_20] :
      ( k1_tops_1(A_20,k2_struct_0(A_20)) = k2_struct_0(A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_220,plain,(
    ! [C_74,A_75,B_76] :
      ( m2_connsp_2(C_74,A_75,B_76)
      | ~ r1_tarski(B_76,k1_tops_1(A_75,C_74))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_411,plain,(
    ! [A_103,B_104] :
      ( m2_connsp_2(k2_struct_0(A_103),A_103,B_104)
      | ~ r1_tarski(B_104,k2_struct_0(A_103))
      | ~ m1_subset_1(k2_struct_0(A_103),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_220])).

tff(c_413,plain,(
    ! [B_104] :
      ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4',B_104)
      | ~ r1_tarski(B_104,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_411])).

tff(c_416,plain,(
    ! [B_105] :
      ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4',B_105)
      | ~ r1_tarski(B_105,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_44,c_42,c_75,c_47,c_413])).

tff(c_419,plain,
    ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5')
    | ~ r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_416])).

tff(c_426,plain,(
    m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_419])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:45:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.35  
% 2.63/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.35  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.63/1.35  
% 2.63/1.35  %Foreground sorts:
% 2.63/1.35  
% 2.63/1.35  
% 2.63/1.35  %Background operators:
% 2.63/1.35  
% 2.63/1.35  
% 2.63/1.35  %Foreground operators:
% 2.63/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.63/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.63/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.63/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.63/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.63/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.63/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.63/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.63/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.63/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.63/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.35  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.63/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.63/1.35  
% 2.77/1.36  tff(f_93, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.77/1.36  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.77/1.36  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.77/1.36  tff(f_44, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.77/1.36  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.77/1.36  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.77/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.77/1.36  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.77/1.36  tff(f_56, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.77/1.36  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.77/1.36  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.77/1.36  tff(c_38, plain, (~m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.36  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.77/1.36  tff(c_20, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.36  tff(c_22, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.36  tff(c_47, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.77/1.36  tff(c_106, plain, (![A_47, B_48]: (r2_hidden(A_47, B_48) | v1_xboole_0(B_48) | ~m1_subset_1(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.77/1.36  tff(c_8, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.77/1.36  tff(c_126, plain, (![A_51, A_52]: (r1_tarski(A_51, A_52) | v1_xboole_0(k1_zfmisc_1(A_52)) | ~m1_subset_1(A_51, k1_zfmisc_1(A_52)))), inference(resolution, [status(thm)], [c_106, c_8])).
% 2.77/1.36  tff(c_135, plain, (![A_53]: (r1_tarski(A_53, A_53) | v1_xboole_0(k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_47, c_126])).
% 2.77/1.36  tff(c_87, plain, (![C_41, A_42]: (r2_hidden(C_41, k1_zfmisc_1(A_42)) | ~r1_tarski(C_41, A_42))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.77/1.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.36  tff(c_95, plain, (![A_42, C_41]: (~v1_xboole_0(k1_zfmisc_1(A_42)) | ~r1_tarski(C_41, A_42))), inference(resolution, [status(thm)], [c_87, c_2])).
% 2.77/1.36  tff(c_139, plain, (![C_54, A_55]: (~r1_tarski(C_54, A_55) | r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_135, c_95])).
% 2.77/1.36  tff(c_148, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_6, c_139])).
% 2.77/1.36  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.36  tff(c_30, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.77/1.36  tff(c_61, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.77/1.36  tff(c_71, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_30, c_61])).
% 2.77/1.36  tff(c_75, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_71])).
% 2.77/1.36  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.36  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_40])).
% 2.77/1.36  tff(c_133, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_76, c_126])).
% 2.77/1.36  tff(c_162, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_133])).
% 2.77/1.36  tff(c_166, plain, (![C_59]: (~r1_tarski(C_59, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_162, c_95])).
% 2.77/1.36  tff(c_178, plain, $false, inference(resolution, [status(thm)], [c_148, c_166])).
% 2.77/1.36  tff(c_179, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_133])).
% 2.77/1.36  tff(c_44, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.36  tff(c_32, plain, (![A_20]: (k1_tops_1(A_20, k2_struct_0(A_20))=k2_struct_0(A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.77/1.36  tff(c_220, plain, (![C_74, A_75, B_76]: (m2_connsp_2(C_74, A_75, B_76) | ~r1_tarski(B_76, k1_tops_1(A_75, C_74)) | ~m1_subset_1(C_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.36  tff(c_411, plain, (![A_103, B_104]: (m2_connsp_2(k2_struct_0(A_103), A_103, B_104) | ~r1_tarski(B_104, k2_struct_0(A_103)) | ~m1_subset_1(k2_struct_0(A_103), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(superposition, [status(thm), theory('equality')], [c_32, c_220])).
% 2.77/1.36  tff(c_413, plain, (![B_104]: (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', B_104) | ~r1_tarski(B_104, k2_struct_0('#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_411])).
% 2.77/1.36  tff(c_416, plain, (![B_105]: (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', B_105) | ~r1_tarski(B_105, k2_struct_0('#skF_4')) | ~m1_subset_1(B_105, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_44, c_42, c_75, c_47, c_413])).
% 2.77/1.36  tff(c_419, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5') | ~r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_416])).
% 2.77/1.36  tff(c_426, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_419])).
% 2.77/1.36  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_426])).
% 2.77/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.36  
% 2.77/1.36  Inference rules
% 2.77/1.36  ----------------------
% 2.77/1.36  #Ref     : 0
% 2.77/1.36  #Sup     : 78
% 2.77/1.36  #Fact    : 0
% 2.77/1.36  #Define  : 0
% 2.77/1.36  #Split   : 3
% 2.77/1.36  #Chain   : 0
% 2.77/1.36  #Close   : 0
% 2.77/1.36  
% 2.77/1.36  Ordering : KBO
% 2.77/1.36  
% 2.77/1.36  Simplification rules
% 2.77/1.36  ----------------------
% 2.77/1.36  #Subsume      : 6
% 2.77/1.36  #Demod        : 46
% 2.77/1.36  #Tautology    : 21
% 2.77/1.36  #SimpNegUnit  : 1
% 2.77/1.36  #BackRed      : 1
% 2.77/1.36  
% 2.77/1.36  #Partial instantiations: 0
% 2.77/1.36  #Strategies tried      : 1
% 2.77/1.37  
% 2.77/1.37  Timing (in seconds)
% 2.77/1.37  ----------------------
% 2.77/1.37  Preprocessing        : 0.31
% 2.77/1.37  Parsing              : 0.16
% 2.77/1.37  CNF conversion       : 0.02
% 2.77/1.37  Main loop            : 0.31
% 2.77/1.37  Inferencing          : 0.12
% 2.77/1.37  Reduction            : 0.09
% 2.77/1.37  Demodulation         : 0.06
% 2.77/1.37  BG Simplification    : 0.02
% 2.77/1.37  Subsumption          : 0.06
% 2.77/1.37  Abstraction          : 0.02
% 2.77/1.37  MUC search           : 0.00
% 2.77/1.37  Cooper               : 0.00
% 2.77/1.37  Total                : 0.65
% 2.77/1.37  Index Insertion      : 0.00
% 2.77/1.37  Index Deletion       : 0.00
% 2.77/1.37  Index Matching       : 0.00
% 2.77/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
