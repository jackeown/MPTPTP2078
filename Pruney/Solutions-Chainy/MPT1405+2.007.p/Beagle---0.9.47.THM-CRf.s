%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:30 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 123 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 240 expanded)
%              Number of equality atoms :    9 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_45,axiom,(
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

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_83,axiom,(
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

tff(c_40,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_118,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_2'(A_48,B_49),B_49)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_131,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_118])).

tff(c_44,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_67,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_32,c_67])).

tff(c_76,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_42])).

tff(c_98,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_205,plain,(
    ! [A_71,A_72] :
      ( r1_tarski(A_71,A_72)
      | v1_xboole_0(k1_zfmisc_1(A_72))
      | ~ m1_subset_1(A_71,k1_zfmisc_1(A_72)) ) ),
    inference(resolution,[status(thm)],[c_98,c_12])).

tff(c_212,plain,
    ( r1_tarski('#skF_6',k2_struct_0('#skF_5'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_77,c_205])).

tff(c_215,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_88,plain,(
    ! [C_40,A_41] :
      ( r2_hidden(C_40,k1_zfmisc_1(A_41))
      | ~ r1_tarski(C_40,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_41,C_40] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_41))
      | ~ r1_tarski(C_40,A_41) ) ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_228,plain,(
    ! [C_75] : ~ r1_tarski(C_75,k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_215,c_96])).

tff(c_243,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_131,c_228])).

tff(c_244,plain,(
    r1_tarski('#skF_6',k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_46,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_16] : m1_subset_1(k2_subset_1(A_16),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    ! [A_16] : m1_subset_1(A_16,k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_34,plain,(
    ! [A_21] :
      ( k1_tops_1(A_21,k2_struct_0(A_21)) = k2_struct_0(A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_474,plain,(
    ! [C_108,A_109,B_110] :
      ( m2_connsp_2(C_108,A_109,B_110)
      | ~ r1_tarski(B_110,k1_tops_1(A_109,C_108))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2236,plain,(
    ! [A_237,B_238] :
      ( m2_connsp_2(k2_struct_0(A_237),A_237,B_238)
      | ~ r1_tarski(B_238,k2_struct_0(A_237))
      | ~ m1_subset_1(k2_struct_0(A_237),k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ l1_pre_topc(A_237)
      | ~ v2_pre_topc(A_237)
      | ~ l1_pre_topc(A_237)
      | ~ v2_pre_topc(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_474])).

tff(c_2238,plain,(
    ! [B_238] :
      ( m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5',B_238)
      | ~ r1_tarski(B_238,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_2236])).

tff(c_2300,plain,(
    ! [B_242] :
      ( m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5',B_242)
      | ~ r1_tarski(B_242,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_46,c_44,c_76,c_49,c_2238])).

tff(c_2303,plain,
    ( m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5','#skF_6')
    | ~ r1_tarski('#skF_6',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_77,c_2300])).

tff(c_2310,plain,(
    m2_connsp_2(k2_struct_0('#skF_5'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_2303])).

tff(c_2312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:12:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.83  
% 4.61/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.84  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.61/1.84  
% 4.61/1.84  %Foreground sorts:
% 4.61/1.84  
% 4.61/1.84  
% 4.61/1.84  %Background operators:
% 4.61/1.84  
% 4.61/1.84  
% 4.61/1.84  %Foreground operators:
% 4.61/1.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.61/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.61/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.61/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.61/1.84  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.61/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.61/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.61/1.84  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.61/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.61/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.61/1.84  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.61/1.84  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.61/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.61/1.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.61/1.84  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 4.61/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.61/1.84  
% 4.70/1.85  tff(f_96, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 4.70/1.85  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.70/1.85  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.70/1.85  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.70/1.85  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.70/1.85  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.70/1.85  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.70/1.85  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.70/1.85  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.70/1.85  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 4.70/1.85  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 4.70/1.85  tff(c_40, plain, (~m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.70/1.85  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/1.85  tff(c_118, plain, (![A_48, B_49]: (~r2_hidden('#skF_2'(A_48, B_49), B_49) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/1.85  tff(c_131, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_118])).
% 4.70/1.85  tff(c_44, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.70/1.85  tff(c_32, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.70/1.85  tff(c_67, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.70/1.85  tff(c_72, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_32, c_67])).
% 4.70/1.85  tff(c_76, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_44, c_72])).
% 4.70/1.85  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.70/1.85  tff(c_77, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_42])).
% 4.70/1.85  tff(c_98, plain, (![A_44, B_45]: (r2_hidden(A_44, B_45) | v1_xboole_0(B_45) | ~m1_subset_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.70/1.85  tff(c_12, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.70/1.85  tff(c_205, plain, (![A_71, A_72]: (r1_tarski(A_71, A_72) | v1_xboole_0(k1_zfmisc_1(A_72)) | ~m1_subset_1(A_71, k1_zfmisc_1(A_72)))), inference(resolution, [status(thm)], [c_98, c_12])).
% 4.70/1.85  tff(c_212, plain, (r1_tarski('#skF_6', k2_struct_0('#skF_5')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_77, c_205])).
% 4.70/1.85  tff(c_215, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_212])).
% 4.70/1.85  tff(c_88, plain, (![C_40, A_41]: (r2_hidden(C_40, k1_zfmisc_1(A_41)) | ~r1_tarski(C_40, A_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.70/1.85  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.70/1.85  tff(c_96, plain, (![A_41, C_40]: (~v1_xboole_0(k1_zfmisc_1(A_41)) | ~r1_tarski(C_40, A_41))), inference(resolution, [status(thm)], [c_88, c_2])).
% 4.70/1.85  tff(c_228, plain, (![C_75]: (~r1_tarski(C_75, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_215, c_96])).
% 4.70/1.85  tff(c_243, plain, $false, inference(resolution, [status(thm)], [c_131, c_228])).
% 4.70/1.85  tff(c_244, plain, (r1_tarski('#skF_6', k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_212])).
% 4.70/1.85  tff(c_46, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.70/1.85  tff(c_24, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.70/1.85  tff(c_26, plain, (![A_16]: (m1_subset_1(k2_subset_1(A_16), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.70/1.85  tff(c_49, plain, (![A_16]: (m1_subset_1(A_16, k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 4.70/1.85  tff(c_34, plain, (![A_21]: (k1_tops_1(A_21, k2_struct_0(A_21))=k2_struct_0(A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.70/1.85  tff(c_474, plain, (![C_108, A_109, B_110]: (m2_connsp_2(C_108, A_109, B_110) | ~r1_tarski(B_110, k1_tops_1(A_109, C_108)) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.70/1.85  tff(c_2236, plain, (![A_237, B_238]: (m2_connsp_2(k2_struct_0(A_237), A_237, B_238) | ~r1_tarski(B_238, k2_struct_0(A_237)) | ~m1_subset_1(k2_struct_0(A_237), k1_zfmisc_1(u1_struct_0(A_237))) | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0(A_237))) | ~l1_pre_topc(A_237) | ~v2_pre_topc(A_237) | ~l1_pre_topc(A_237) | ~v2_pre_topc(A_237))), inference(superposition, [status(thm), theory('equality')], [c_34, c_474])).
% 4.70/1.85  tff(c_2238, plain, (![B_238]: (m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', B_238) | ~r1_tarski(B_238, k2_struct_0('#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_2236])).
% 4.70/1.85  tff(c_2300, plain, (![B_242]: (m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', B_242) | ~r1_tarski(B_242, k2_struct_0('#skF_5')) | ~m1_subset_1(B_242, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_46, c_44, c_76, c_49, c_2238])).
% 4.70/1.85  tff(c_2303, plain, (m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', '#skF_6') | ~r1_tarski('#skF_6', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_77, c_2300])).
% 4.70/1.85  tff(c_2310, plain, (m2_connsp_2(k2_struct_0('#skF_5'), '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_2303])).
% 4.70/1.85  tff(c_2312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_2310])).
% 4.70/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.85  
% 4.70/1.85  Inference rules
% 4.70/1.85  ----------------------
% 4.70/1.85  #Ref     : 0
% 4.70/1.85  #Sup     : 561
% 4.70/1.85  #Fact    : 0
% 4.70/1.85  #Define  : 0
% 4.70/1.85  #Split   : 11
% 4.70/1.85  #Chain   : 0
% 4.70/1.85  #Close   : 0
% 4.70/1.85  
% 4.70/1.85  Ordering : KBO
% 4.70/1.85  
% 4.70/1.85  Simplification rules
% 4.70/1.85  ----------------------
% 4.70/1.85  #Subsume      : 180
% 4.70/1.85  #Demod        : 33
% 4.70/1.85  #Tautology    : 28
% 4.70/1.85  #SimpNegUnit  : 21
% 4.70/1.85  #BackRed      : 5
% 4.70/1.85  
% 4.70/1.85  #Partial instantiations: 0
% 4.70/1.85  #Strategies tried      : 1
% 4.70/1.85  
% 4.70/1.85  Timing (in seconds)
% 4.70/1.85  ----------------------
% 4.70/1.85  Preprocessing        : 0.33
% 4.70/1.85  Parsing              : 0.17
% 4.70/1.85  CNF conversion       : 0.03
% 4.70/1.85  Main loop            : 0.75
% 4.70/1.85  Inferencing          : 0.24
% 4.70/1.85  Reduction            : 0.21
% 4.70/1.85  Demodulation         : 0.13
% 4.70/1.85  BG Simplification    : 0.03
% 4.70/1.85  Subsumption          : 0.22
% 4.70/1.85  Abstraction          : 0.04
% 4.70/1.85  MUC search           : 0.00
% 4.70/1.85  Cooper               : 0.00
% 4.70/1.85  Total                : 1.11
% 4.70/1.85  Index Insertion      : 0.00
% 4.70/1.85  Index Deletion       : 0.00
% 4.70/1.85  Index Matching       : 0.00
% 4.70/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
