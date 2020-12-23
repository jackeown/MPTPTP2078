%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:32 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 132 expanded)
%              Number of leaves         :   31 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 273 expanded)
%              Number of equality atoms :    8 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

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

tff(c_28,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_49,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_55,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_18,c_49])).

tff(c_59,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_55])).

tff(c_20,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_20])).

tff(c_67,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_64])).

tff(c_69,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_72,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_69])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_72])).

tff(c_77,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_30])).

tff(c_105,plain,(
    ! [A_41,C_42,B_43] :
      ( m1_subset_1(A_41,C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_110,plain,(
    ! [A_41] :
      ( m1_subset_1(A_41,k2_struct_0('#skF_2'))
      | ~ r2_hidden(A_41,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_60,c_105])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_33,B_34] :
      ( ~ r2_hidden('#skF_1'(A_33,B_34),B_34)
      | r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | v1_xboole_0(B_51)
      | ~ m1_subset_1('#skF_1'(A_50,B_51),B_51) ) ),
    inference(resolution,[status(thm)],[c_12,c_85])).

tff(c_144,plain,(
    ! [A_50] :
      ( r1_tarski(A_50,k2_struct_0('#skF_2'))
      | v1_xboole_0(k2_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_1'(A_50,k2_struct_0('#skF_2')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_110,c_136])).

tff(c_150,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,k2_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_1'(A_52,k2_struct_0('#skF_2')),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_144])).

tff(c_158,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_37,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_22,plain,(
    ! [A_16] :
      ( k1_tops_1(A_16,k2_struct_0(A_16)) = k2_struct_0(A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_190,plain,(
    ! [C_60,A_61,B_62] :
      ( m2_connsp_2(C_60,A_61,B_62)
      | ~ r1_tarski(B_62,k1_tops_1(A_61,C_60))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_497,plain,(
    ! [A_105,B_106] :
      ( m2_connsp_2(k2_struct_0(A_105),A_105,B_106)
      | ~ r1_tarski(B_106,k2_struct_0(A_105))
      | ~ m1_subset_1(k2_struct_0(A_105),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_190])).

tff(c_499,plain,(
    ! [B_106] :
      ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2',B_106)
      | ~ r1_tarski(B_106,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_497])).

tff(c_502,plain,(
    ! [B_107] :
      ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2',B_107)
      | ~ r1_tarski(B_107,k2_struct_0('#skF_2'))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_34,c_32,c_59,c_37,c_499])).

tff(c_513,plain,
    ( m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_502])).

tff(c_522,plain,(
    m2_connsp_2(k2_struct_0('#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_513])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:12:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.43  
% 2.64/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.43  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.64/1.43  
% 2.64/1.43  %Foreground sorts:
% 2.64/1.43  
% 2.64/1.43  
% 2.64/1.43  %Background operators:
% 2.64/1.43  
% 2.64/1.43  
% 2.64/1.43  %Foreground operators:
% 2.64/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.64/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.43  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.64/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.64/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.64/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.64/1.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.64/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.64/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.64/1.43  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.64/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.43  
% 2.64/1.45  tff(f_97, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.64/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.64/1.45  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.64/1.45  tff(f_52, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.64/1.45  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.64/1.45  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.64/1.45  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.64/1.45  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.64/1.45  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.64/1.45  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.64/1.45  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.64/1.45  tff(c_28, plain, (~m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.64/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.45  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.64/1.45  tff(c_18, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.45  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.64/1.45  tff(c_49, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.64/1.45  tff(c_55, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_18, c_49])).
% 2.64/1.45  tff(c_59, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_55])).
% 2.64/1.45  tff(c_20, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.64/1.45  tff(c_64, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_59, c_20])).
% 2.64/1.45  tff(c_67, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_64])).
% 2.64/1.45  tff(c_69, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_67])).
% 2.64/1.45  tff(c_72, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_69])).
% 2.64/1.45  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_72])).
% 2.64/1.45  tff(c_77, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_67])).
% 2.64/1.45  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.64/1.45  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_30])).
% 2.64/1.45  tff(c_105, plain, (![A_41, C_42, B_43]: (m1_subset_1(A_41, C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.64/1.45  tff(c_110, plain, (![A_41]: (m1_subset_1(A_41, k2_struct_0('#skF_2')) | ~r2_hidden(A_41, '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_105])).
% 2.64/1.45  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.64/1.45  tff(c_85, plain, (![A_33, B_34]: (~r2_hidden('#skF_1'(A_33, B_34), B_34) | r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.45  tff(c_136, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | v1_xboole_0(B_51) | ~m1_subset_1('#skF_1'(A_50, B_51), B_51))), inference(resolution, [status(thm)], [c_12, c_85])).
% 2.64/1.45  tff(c_144, plain, (![A_50]: (r1_tarski(A_50, k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(A_50, k2_struct_0('#skF_2')), '#skF_3'))), inference(resolution, [status(thm)], [c_110, c_136])).
% 2.64/1.45  tff(c_150, plain, (![A_52]: (r1_tarski(A_52, k2_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(A_52, k2_struct_0('#skF_2')), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_77, c_144])).
% 2.64/1.45  tff(c_158, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_150])).
% 2.64/1.45  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.64/1.45  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.64/1.45  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.64/1.45  tff(c_37, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.64/1.45  tff(c_22, plain, (![A_16]: (k1_tops_1(A_16, k2_struct_0(A_16))=k2_struct_0(A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.64/1.45  tff(c_190, plain, (![C_60, A_61, B_62]: (m2_connsp_2(C_60, A_61, B_62) | ~r1_tarski(B_62, k1_tops_1(A_61, C_60)) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.64/1.45  tff(c_497, plain, (![A_105, B_106]: (m2_connsp_2(k2_struct_0(A_105), A_105, B_106) | ~r1_tarski(B_106, k2_struct_0(A_105)) | ~m1_subset_1(k2_struct_0(A_105), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105))), inference(superposition, [status(thm), theory('equality')], [c_22, c_190])).
% 2.64/1.45  tff(c_499, plain, (![B_106]: (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', B_106) | ~r1_tarski(B_106, k2_struct_0('#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_497])).
% 2.64/1.45  tff(c_502, plain, (![B_107]: (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', B_107) | ~r1_tarski(B_107, k2_struct_0('#skF_2')) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_34, c_32, c_59, c_37, c_499])).
% 2.64/1.45  tff(c_513, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_502])).
% 2.64/1.45  tff(c_522, plain, (m2_connsp_2(k2_struct_0('#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_513])).
% 2.64/1.45  tff(c_524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_522])).
% 2.64/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.45  
% 2.64/1.45  Inference rules
% 2.64/1.45  ----------------------
% 2.64/1.45  #Ref     : 0
% 2.64/1.45  #Sup     : 105
% 2.64/1.45  #Fact    : 0
% 2.64/1.45  #Define  : 0
% 2.64/1.45  #Split   : 6
% 2.64/1.45  #Chain   : 0
% 2.64/1.45  #Close   : 0
% 2.64/1.45  
% 2.64/1.45  Ordering : KBO
% 2.64/1.45  
% 2.64/1.45  Simplification rules
% 2.64/1.45  ----------------------
% 2.64/1.45  #Subsume      : 15
% 2.64/1.45  #Demod        : 32
% 2.64/1.45  #Tautology    : 15
% 2.64/1.45  #SimpNegUnit  : 6
% 2.64/1.45  #BackRed      : 1
% 2.64/1.45  
% 2.64/1.45  #Partial instantiations: 0
% 2.64/1.45  #Strategies tried      : 1
% 2.64/1.45  
% 2.64/1.45  Timing (in seconds)
% 2.64/1.45  ----------------------
% 2.64/1.45  Preprocessing        : 0.32
% 2.64/1.45  Parsing              : 0.18
% 2.64/1.45  CNF conversion       : 0.02
% 2.64/1.45  Main loop            : 0.32
% 2.64/1.45  Inferencing          : 0.12
% 2.64/1.45  Reduction            : 0.09
% 2.64/1.45  Demodulation         : 0.06
% 2.64/1.45  BG Simplification    : 0.02
% 2.64/1.45  Subsumption          : 0.07
% 2.64/1.45  Abstraction          : 0.02
% 2.64/1.45  MUC search           : 0.00
% 2.64/1.45  Cooper               : 0.00
% 2.64/1.45  Total                : 0.67
% 2.64/1.45  Index Insertion      : 0.00
% 2.64/1.45  Index Deletion       : 0.00
% 2.64/1.45  Index Matching       : 0.00
% 2.64/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
