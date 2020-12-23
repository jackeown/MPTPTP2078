%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:31 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 137 expanded)
%              Number of leaves         :   33 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 274 expanded)
%              Number of equality atoms :    9 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_86,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_67,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_32,c_62])).

tff(c_71,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_67])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_42])).

tff(c_83,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_72,c_83])).

tff(c_93,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_104,plain,(
    ! [B_42,A_43] :
      ( r2_hidden(B_42,A_43)
      | ~ m1_subset_1(B_42,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( r1_tarski(C_6,A_2)
      | ~ r2_hidden(C_6,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_167,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(B_56,A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | v1_xboole_0(k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_177,plain,
    ( r1_tarski('#skF_4',k2_struct_0('#skF_3'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_72,c_167])).

tff(c_185,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_177])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_49,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_34,plain,(
    ! [A_16] :
      ( k1_tops_1(A_16,k2_struct_0(A_16)) = k2_struct_0(A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_262,plain,(
    ! [C_77,A_78,B_79] :
      ( m2_connsp_2(C_77,A_78,B_79)
      | ~ r1_tarski(B_79,k1_tops_1(A_78,C_77))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1112,plain,(
    ! [A_134,B_135] :
      ( m2_connsp_2(k2_struct_0(A_134),A_134,B_135)
      | ~ r1_tarski(B_135,k2_struct_0(A_134))
      | ~ m1_subset_1(k2_struct_0(A_134),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_262])).

tff(c_1120,plain,(
    ! [B_135] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_135)
      | ~ r1_tarski(B_135,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1112])).

tff(c_1126,plain,(
    ! [B_137] :
      ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3',B_137)
      | ~ r1_tarski(B_137,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_46,c_44,c_71,c_49,c_1120])).

tff(c_1148,plain,
    ( m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_1126])).

tff(c_1168,plain,(
    m2_connsp_2(k2_struct_0('#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_1148])).

tff(c_1170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1168])).

tff(c_1172,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( r2_hidden(C_6,k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1197,plain,(
    ! [C_144,B_145,A_146] :
      ( ~ v1_xboole_0(C_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(C_144))
      | ~ r2_hidden(A_146,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1217,plain,(
    ! [A_148,A_149] :
      ( ~ v1_xboole_0(A_148)
      | ~ r2_hidden(A_149,A_148) ) ),
    inference(resolution,[status(thm)],[c_49,c_1197])).

tff(c_1226,plain,(
    ! [A_150,C_151] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_150))
      | ~ r1_tarski(C_151,A_150) ) ),
    inference(resolution,[status(thm)],[c_6,c_1217])).

tff(c_1230,plain,(
    ! [C_152] : ~ r1_tarski(C_152,k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1172,c_1226])).

tff(c_1235,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_2,c_1230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:46:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.58  
% 3.70/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.58  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.70/1.58  
% 3.70/1.58  %Foreground sorts:
% 3.70/1.58  
% 3.70/1.58  
% 3.70/1.58  %Background operators:
% 3.70/1.58  
% 3.70/1.58  
% 3.70/1.58  %Foreground operators:
% 3.70/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.70/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.70/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.58  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.70/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.58  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.70/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.70/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.70/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.70/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.70/1.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.70/1.58  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.70/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.70/1.58  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.70/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.58  
% 3.70/1.59  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.70/1.59  tff(f_99, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 3.70/1.59  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.70/1.59  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.70/1.59  tff(f_47, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.70/1.59  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.70/1.59  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.70/1.59  tff(f_51, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.70/1.59  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.70/1.59  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.70/1.59  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.70/1.59  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.70/1.59  tff(c_40, plain, (~m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.70/1.59  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.70/1.59  tff(c_32, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.70/1.59  tff(c_62, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.70/1.59  tff(c_67, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_32, c_62])).
% 3.70/1.59  tff(c_71, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_67])).
% 3.70/1.59  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.70/1.59  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_42])).
% 3.70/1.59  tff(c_83, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.70/1.59  tff(c_90, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_72, c_83])).
% 3.70/1.59  tff(c_93, plain, (~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_90])).
% 3.70/1.59  tff(c_104, plain, (![B_42, A_43]: (r2_hidden(B_42, A_43) | ~m1_subset_1(B_42, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.70/1.59  tff(c_4, plain, (![C_6, A_2]: (r1_tarski(C_6, A_2) | ~r2_hidden(C_6, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.70/1.59  tff(c_167, plain, (![B_56, A_57]: (r1_tarski(B_56, A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | v1_xboole_0(k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_104, c_4])).
% 3.70/1.59  tff(c_177, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_72, c_167])).
% 3.70/1.59  tff(c_185, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_93, c_177])).
% 3.70/1.59  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.70/1.59  tff(c_24, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.70/1.59  tff(c_26, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.70/1.59  tff(c_49, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 3.70/1.59  tff(c_34, plain, (![A_16]: (k1_tops_1(A_16, k2_struct_0(A_16))=k2_struct_0(A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.70/1.59  tff(c_262, plain, (![C_77, A_78, B_79]: (m2_connsp_2(C_77, A_78, B_79) | ~r1_tarski(B_79, k1_tops_1(A_78, C_77)) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.70/1.59  tff(c_1112, plain, (![A_134, B_135]: (m2_connsp_2(k2_struct_0(A_134), A_134, B_135) | ~r1_tarski(B_135, k2_struct_0(A_134)) | ~m1_subset_1(k2_struct_0(A_134), k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134))), inference(superposition, [status(thm), theory('equality')], [c_34, c_262])).
% 3.70/1.59  tff(c_1120, plain, (![B_135]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_135) | ~r1_tarski(B_135, k2_struct_0('#skF_3')) | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1112])).
% 3.70/1.59  tff(c_1126, plain, (![B_137]: (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', B_137) | ~r1_tarski(B_137, k2_struct_0('#skF_3')) | ~m1_subset_1(B_137, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_46, c_44, c_71, c_49, c_1120])).
% 3.70/1.59  tff(c_1148, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_1126])).
% 3.70/1.59  tff(c_1168, plain, (m2_connsp_2(k2_struct_0('#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_1148])).
% 3.70/1.59  tff(c_1170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1168])).
% 3.70/1.59  tff(c_1172, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_90])).
% 3.70/1.59  tff(c_6, plain, (![C_6, A_2]: (r2_hidden(C_6, k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.70/1.59  tff(c_1197, plain, (![C_144, B_145, A_146]: (~v1_xboole_0(C_144) | ~m1_subset_1(B_145, k1_zfmisc_1(C_144)) | ~r2_hidden(A_146, B_145))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.70/1.59  tff(c_1217, plain, (![A_148, A_149]: (~v1_xboole_0(A_148) | ~r2_hidden(A_149, A_148))), inference(resolution, [status(thm)], [c_49, c_1197])).
% 3.70/1.59  tff(c_1226, plain, (![A_150, C_151]: (~v1_xboole_0(k1_zfmisc_1(A_150)) | ~r1_tarski(C_151, A_150))), inference(resolution, [status(thm)], [c_6, c_1217])).
% 3.70/1.59  tff(c_1230, plain, (![C_152]: (~r1_tarski(C_152, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1172, c_1226])).
% 3.70/1.59  tff(c_1235, plain, $false, inference(resolution, [status(thm)], [c_2, c_1230])).
% 3.70/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.59  
% 3.70/1.59  Inference rules
% 3.70/1.59  ----------------------
% 3.70/1.59  #Ref     : 0
% 3.70/1.59  #Sup     : 245
% 3.70/1.59  #Fact    : 0
% 3.70/1.59  #Define  : 0
% 3.70/1.59  #Split   : 12
% 3.70/1.59  #Chain   : 0
% 3.70/1.59  #Close   : 0
% 3.70/1.59  
% 3.70/1.59  Ordering : KBO
% 3.70/1.59  
% 3.70/1.59  Simplification rules
% 3.70/1.59  ----------------------
% 3.70/1.59  #Subsume      : 40
% 3.70/1.59  #Demod        : 103
% 3.70/1.59  #Tautology    : 53
% 3.70/1.59  #SimpNegUnit  : 31
% 3.70/1.59  #BackRed      : 10
% 3.70/1.59  
% 3.70/1.59  #Partial instantiations: 0
% 3.70/1.59  #Strategies tried      : 1
% 3.70/1.59  
% 3.70/1.59  Timing (in seconds)
% 3.70/1.59  ----------------------
% 3.70/1.59  Preprocessing        : 0.31
% 3.70/1.59  Parsing              : 0.16
% 3.70/1.59  CNF conversion       : 0.02
% 3.70/1.60  Main loop            : 0.52
% 3.70/1.60  Inferencing          : 0.18
% 3.70/1.60  Reduction            : 0.15
% 3.70/1.60  Demodulation         : 0.10
% 3.70/1.60  BG Simplification    : 0.02
% 3.70/1.60  Subsumption          : 0.12
% 3.70/1.60  Abstraction          : 0.03
% 3.70/1.60  MUC search           : 0.00
% 3.70/1.60  Cooper               : 0.00
% 3.70/1.60  Total                : 0.86
% 3.70/1.60  Index Insertion      : 0.00
% 3.70/1.60  Index Deletion       : 0.00
% 3.70/1.60  Index Matching       : 0.00
% 3.70/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
