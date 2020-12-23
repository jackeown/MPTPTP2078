%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:32 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 128 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  107 ( 249 expanded)
%              Number of equality atoms :    9 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_84,axiom,(
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

tff(c_38,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_97,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),A_42)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [A_42] : r1_tarski(A_42,A_42) ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_59,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_65,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_69,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_65])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_40])).

tff(c_86,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_175,plain,(
    ! [A_68,A_69] :
      ( r1_tarski(A_68,A_69)
      | v1_xboole_0(k1_zfmisc_1(A_69))
      | ~ m1_subset_1(A_68,k1_zfmisc_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_86,c_8])).

tff(c_182,plain,
    ( r1_tarski('#skF_5',k2_struct_0('#skF_4'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_70,c_175])).

tff(c_185,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_119,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_126,plain,(
    ! [A_51,A_52] :
      ( ~ v1_xboole_0(A_51)
      | ~ r2_hidden(A_52,A_51) ) ),
    inference(resolution,[status(thm)],[c_47,c_119])).

tff(c_138,plain,(
    ! [A_6,C_10] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_189,plain,(
    ! [C_70] : ~ r1_tarski(C_70,k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_185,c_138])).

tff(c_203,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_106,c_189])).

tff(c_204,plain,(
    r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_44,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [A_20] :
      ( k1_tops_1(A_20,k2_struct_0(A_20)) = k2_struct_0(A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_390,plain,(
    ! [C_108,A_109,B_110] :
      ( m2_connsp_2(C_108,A_109,B_110)
      | ~ r1_tarski(B_110,k1_tops_1(A_109,C_108))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1664,plain,(
    ! [A_212,B_213] :
      ( m2_connsp_2(k2_struct_0(A_212),A_212,B_213)
      | ~ r1_tarski(B_213,k2_struct_0(A_212))
      | ~ m1_subset_1(k2_struct_0(A_212),k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212)
      | ~ v2_pre_topc(A_212)
      | ~ l1_pre_topc(A_212)
      | ~ v2_pre_topc(A_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_390])).

tff(c_1666,plain,(
    ! [B_213] :
      ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4',B_213)
      | ~ r1_tarski(B_213,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_1664])).

tff(c_1669,plain,(
    ! [B_214] :
      ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4',B_214)
      | ~ r1_tarski(B_214,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_44,c_42,c_69,c_47,c_1666])).

tff(c_1672,plain,
    ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5')
    | ~ r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_1669])).

tff(c_1679,plain,(
    m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_1672])).

tff(c_1681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:33:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.68  
% 3.89/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.68  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.89/1.68  
% 3.89/1.68  %Foreground sorts:
% 3.89/1.68  
% 3.89/1.68  
% 3.89/1.68  %Background operators:
% 3.89/1.68  
% 3.89/1.68  
% 3.89/1.68  %Foreground operators:
% 3.89/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.89/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.89/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.89/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.89/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.89/1.68  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.89/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.89/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.89/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.89/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.89/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.89/1.68  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.89/1.68  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.89/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.89/1.68  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.89/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.68  
% 3.89/1.70  tff(f_97, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 3.89/1.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.89/1.70  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.89/1.70  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.89/1.70  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.89/1.70  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.89/1.70  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.89/1.70  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.89/1.70  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.89/1.70  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.89/1.70  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.89/1.70  tff(c_38, plain, (~m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.89/1.70  tff(c_97, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), A_42) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.89/1.70  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.89/1.70  tff(c_106, plain, (![A_42]: (r1_tarski(A_42, A_42))), inference(resolution, [status(thm)], [c_97, c_4])).
% 3.89/1.70  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.89/1.70  tff(c_30, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.89/1.70  tff(c_59, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.89/1.70  tff(c_65, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_30, c_59])).
% 3.89/1.70  tff(c_69, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_65])).
% 3.89/1.70  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.89/1.70  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_40])).
% 3.89/1.70  tff(c_86, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | v1_xboole_0(B_41) | ~m1_subset_1(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.89/1.70  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.89/1.70  tff(c_175, plain, (![A_68, A_69]: (r1_tarski(A_68, A_69) | v1_xboole_0(k1_zfmisc_1(A_69)) | ~m1_subset_1(A_68, k1_zfmisc_1(A_69)))), inference(resolution, [status(thm)], [c_86, c_8])).
% 3.89/1.70  tff(c_182, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_70, c_175])).
% 3.89/1.70  tff(c_185, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_182])).
% 3.89/1.70  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.89/1.70  tff(c_20, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.89/1.70  tff(c_22, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.89/1.70  tff(c_47, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 3.89/1.70  tff(c_119, plain, (![C_48, B_49, A_50]: (~v1_xboole_0(C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.89/1.70  tff(c_126, plain, (![A_51, A_52]: (~v1_xboole_0(A_51) | ~r2_hidden(A_52, A_51))), inference(resolution, [status(thm)], [c_47, c_119])).
% 3.89/1.70  tff(c_138, plain, (![A_6, C_10]: (~v1_xboole_0(k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(resolution, [status(thm)], [c_10, c_126])).
% 3.89/1.70  tff(c_189, plain, (![C_70]: (~r1_tarski(C_70, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_185, c_138])).
% 3.89/1.70  tff(c_203, plain, $false, inference(resolution, [status(thm)], [c_106, c_189])).
% 3.89/1.70  tff(c_204, plain, (r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_182])).
% 3.89/1.70  tff(c_44, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.89/1.70  tff(c_32, plain, (![A_20]: (k1_tops_1(A_20, k2_struct_0(A_20))=k2_struct_0(A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.89/1.70  tff(c_390, plain, (![C_108, A_109, B_110]: (m2_connsp_2(C_108, A_109, B_110) | ~r1_tarski(B_110, k1_tops_1(A_109, C_108)) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.89/1.70  tff(c_1664, plain, (![A_212, B_213]: (m2_connsp_2(k2_struct_0(A_212), A_212, B_213) | ~r1_tarski(B_213, k2_struct_0(A_212)) | ~m1_subset_1(k2_struct_0(A_212), k1_zfmisc_1(u1_struct_0(A_212))) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212) | ~v2_pre_topc(A_212) | ~l1_pre_topc(A_212) | ~v2_pre_topc(A_212))), inference(superposition, [status(thm), theory('equality')], [c_32, c_390])).
% 3.89/1.70  tff(c_1666, plain, (![B_213]: (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', B_213) | ~r1_tarski(B_213, k2_struct_0('#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_1664])).
% 3.89/1.70  tff(c_1669, plain, (![B_214]: (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', B_214) | ~r1_tarski(B_214, k2_struct_0('#skF_4')) | ~m1_subset_1(B_214, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_44, c_42, c_69, c_47, c_1666])).
% 3.89/1.70  tff(c_1672, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5') | ~r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_1669])).
% 3.89/1.70  tff(c_1679, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_1672])).
% 3.89/1.70  tff(c_1681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1679])).
% 3.89/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.70  
% 3.89/1.70  Inference rules
% 3.89/1.70  ----------------------
% 3.89/1.70  #Ref     : 0
% 3.89/1.70  #Sup     : 397
% 3.89/1.70  #Fact    : 0
% 3.89/1.70  #Define  : 0
% 3.89/1.70  #Split   : 16
% 3.89/1.70  #Chain   : 0
% 3.89/1.70  #Close   : 0
% 3.89/1.70  
% 3.89/1.70  Ordering : KBO
% 3.89/1.70  
% 3.89/1.70  Simplification rules
% 3.89/1.70  ----------------------
% 3.89/1.70  #Subsume      : 138
% 3.89/1.70  #Demod        : 33
% 3.89/1.70  #Tautology    : 21
% 3.89/1.70  #SimpNegUnit  : 12
% 3.89/1.70  #BackRed      : 2
% 3.89/1.70  
% 3.89/1.70  #Partial instantiations: 0
% 3.89/1.70  #Strategies tried      : 1
% 3.89/1.70  
% 3.89/1.70  Timing (in seconds)
% 3.89/1.70  ----------------------
% 3.89/1.70  Preprocessing        : 0.32
% 3.89/1.70  Parsing              : 0.16
% 3.89/1.70  CNF conversion       : 0.02
% 3.89/1.70  Main loop            : 0.63
% 3.89/1.70  Inferencing          : 0.21
% 3.89/1.70  Reduction            : 0.17
% 3.89/1.70  Demodulation         : 0.11
% 3.89/1.70  BG Simplification    : 0.03
% 3.89/1.70  Subsumption          : 0.18
% 3.89/1.70  Abstraction          : 0.03
% 3.89/1.70  MUC search           : 0.00
% 3.89/1.70  Cooper               : 0.00
% 3.89/1.70  Total                : 0.98
% 3.89/1.70  Index Insertion      : 0.00
% 3.89/1.70  Index Deletion       : 0.00
% 3.89/1.70  Index Matching       : 0.00
% 3.89/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
