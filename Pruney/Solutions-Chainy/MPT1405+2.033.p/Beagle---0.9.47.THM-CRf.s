%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:34 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 109 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  106 ( 248 expanded)
%              Number of equality atoms :   12 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_24,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_44,B_45,C_46] :
      ( k4_subset_1(A_44,B_45,C_46) = k2_xboole_0(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_644,plain,(
    ! [A_73,B_74,B_75] :
      ( k4_subset_1(A_73,B_74,k3_subset_1(A_73,B_75)) = k2_xboole_0(B_74,k3_subset_1(A_73,B_75))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_73)) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_727,plain,(
    ! [B_76] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k3_subset_1(u1_struct_0('#skF_1'),B_76)) = k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),B_76))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_644])).

tff(c_16,plain,(
    ! [A_14,B_16] :
      ( k4_subset_1(u1_struct_0(A_14),B_16,k3_subset_1(u1_struct_0(A_14),B_16)) = k2_struct_0(A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_734,plain,
    ( k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_16])).

tff(c_750,plain,
    ( k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_734])).

tff(c_758,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_750])).

tff(c_761,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_758])).

tff(c_765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_761])).

tff(c_766,plain,(
    k2_xboole_0('#skF_2',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_776,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_2])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_767,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_176,plain,(
    ! [A_49,B_50] :
      ( k4_subset_1(u1_struct_0(A_49),B_50,k3_subset_1(u1_struct_0(A_49),B_50)) = k2_struct_0(A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k4_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1133,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1(k2_struct_0(A_90),k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_90),B_91),k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_struct_0(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_6])).

tff(c_1176,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k2_struct_0(A_92),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_struct_0(A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1133])).

tff(c_1201,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1176])).

tff(c_1228,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_1201])).

tff(c_18,plain,(
    ! [A_17] :
      ( k1_tops_1(A_17,k2_struct_0(A_17)) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_333,plain,(
    ! [C_58,A_59,B_60] :
      ( m2_connsp_2(C_58,A_59,B_60)
      | ~ r1_tarski(B_60,k1_tops_1(A_59,C_58))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1286,plain,(
    ! [A_94,B_95] :
      ( m2_connsp_2(k2_struct_0(A_94),A_94,B_95)
      | ~ r1_tarski(B_95,k2_struct_0(A_94))
      | ~ m1_subset_1(k2_struct_0(A_94),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_333])).

tff(c_1288,plain,(
    ! [B_95] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_95)
      | ~ r1_tarski(B_95,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1228,c_1286])).

tff(c_1658,plain,(
    ! [B_102] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_102)
      | ~ r1_tarski(B_102,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1288])).

tff(c_1706,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_1658])).

tff(c_1727,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_1706])).

tff(c_1729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.69  
% 3.95/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.69  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.95/1.69  
% 3.95/1.69  %Foreground sorts:
% 3.95/1.69  
% 3.95/1.69  
% 3.95/1.69  %Background operators:
% 3.95/1.69  
% 3.95/1.69  
% 3.95/1.69  %Foreground operators:
% 3.95/1.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.95/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.95/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.69  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.95/1.69  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.95/1.69  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.95/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.69  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.95/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.95/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.95/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.95/1.69  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.95/1.69  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.95/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.69  
% 3.95/1.70  tff(f_91, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 3.95/1.70  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.95/1.70  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.95/1.70  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.95/1.70  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_pre_topc)).
% 3.95/1.70  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.95/1.70  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 3.95/1.70  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 3.95/1.70  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.95/1.70  tff(c_24, plain, (~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.95/1.70  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.95/1.70  tff(c_14, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.95/1.70  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.95/1.70  tff(c_4, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.70  tff(c_66, plain, (![A_44, B_45, C_46]: (k4_subset_1(A_44, B_45, C_46)=k2_xboole_0(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.95/1.70  tff(c_644, plain, (![A_73, B_74, B_75]: (k4_subset_1(A_73, B_74, k3_subset_1(A_73, B_75))=k2_xboole_0(B_74, k3_subset_1(A_73, B_75)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_73)))), inference(resolution, [status(thm)], [c_4, c_66])).
% 3.95/1.70  tff(c_727, plain, (![B_76]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k3_subset_1(u1_struct_0('#skF_1'), B_76))=k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), B_76)) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_26, c_644])).
% 3.95/1.70  tff(c_16, plain, (![A_14, B_16]: (k4_subset_1(u1_struct_0(A_14), B_16, k3_subset_1(u1_struct_0(A_14), B_16))=k2_struct_0(A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.95/1.70  tff(c_734, plain, (k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_727, c_16])).
% 3.95/1.70  tff(c_750, plain, (k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_734])).
% 3.95/1.70  tff(c_758, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_750])).
% 3.95/1.70  tff(c_761, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_758])).
% 3.95/1.70  tff(c_765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_761])).
% 3.95/1.70  tff(c_766, plain, (k2_xboole_0('#skF_2', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_750])).
% 3.95/1.70  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.95/1.70  tff(c_776, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_766, c_2])).
% 3.95/1.70  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.95/1.70  tff(c_767, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_750])).
% 3.95/1.70  tff(c_176, plain, (![A_49, B_50]: (k4_subset_1(u1_struct_0(A_49), B_50, k3_subset_1(u1_struct_0(A_49), B_50))=k2_struct_0(A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.95/1.70  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k4_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.95/1.70  tff(c_1133, plain, (![A_90, B_91]: (m1_subset_1(k2_struct_0(A_90), k1_zfmisc_1(u1_struct_0(A_90))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_90), B_91), k1_zfmisc_1(u1_struct_0(A_90))) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_struct_0(A_90))), inference(superposition, [status(thm), theory('equality')], [c_176, c_6])).
% 3.95/1.70  tff(c_1176, plain, (![A_92, B_93]: (m1_subset_1(k2_struct_0(A_92), k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_struct_0(A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))))), inference(resolution, [status(thm)], [c_4, c_1133])).
% 3.95/1.70  tff(c_1201, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1176])).
% 3.95/1.70  tff(c_1228, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_767, c_1201])).
% 3.95/1.70  tff(c_18, plain, (![A_17]: (k1_tops_1(A_17, k2_struct_0(A_17))=k2_struct_0(A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.95/1.70  tff(c_333, plain, (![C_58, A_59, B_60]: (m2_connsp_2(C_58, A_59, B_60) | ~r1_tarski(B_60, k1_tops_1(A_59, C_58)) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.95/1.70  tff(c_1286, plain, (![A_94, B_95]: (m2_connsp_2(k2_struct_0(A_94), A_94, B_95) | ~r1_tarski(B_95, k2_struct_0(A_94)) | ~m1_subset_1(k2_struct_0(A_94), k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(superposition, [status(thm), theory('equality')], [c_18, c_333])).
% 3.95/1.70  tff(c_1288, plain, (![B_95]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_95) | ~r1_tarski(B_95, k2_struct_0('#skF_1')) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1228, c_1286])).
% 3.95/1.70  tff(c_1658, plain, (![B_102]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_102) | ~r1_tarski(B_102, k2_struct_0('#skF_1')) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1288])).
% 3.95/1.70  tff(c_1706, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1658])).
% 3.95/1.70  tff(c_1727, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_776, c_1706])).
% 3.95/1.70  tff(c_1729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1727])).
% 3.95/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.70  
% 3.95/1.70  Inference rules
% 3.95/1.70  ----------------------
% 3.95/1.70  #Ref     : 0
% 3.95/1.70  #Sup     : 401
% 3.95/1.70  #Fact    : 0
% 3.95/1.70  #Define  : 0
% 3.95/1.70  #Split   : 7
% 3.95/1.70  #Chain   : 0
% 3.95/1.70  #Close   : 0
% 3.95/1.70  
% 3.95/1.70  Ordering : KBO
% 3.95/1.70  
% 3.95/1.70  Simplification rules
% 3.95/1.70  ----------------------
% 3.95/1.70  #Subsume      : 10
% 3.95/1.70  #Demod        : 250
% 3.95/1.70  #Tautology    : 106
% 3.95/1.70  #SimpNegUnit  : 1
% 3.95/1.70  #BackRed      : 0
% 3.95/1.70  
% 3.95/1.70  #Partial instantiations: 0
% 3.95/1.70  #Strategies tried      : 1
% 3.95/1.70  
% 3.95/1.70  Timing (in seconds)
% 3.95/1.70  ----------------------
% 3.95/1.71  Preprocessing        : 0.32
% 3.95/1.71  Parsing              : 0.18
% 3.95/1.71  CNF conversion       : 0.02
% 3.95/1.71  Main loop            : 0.58
% 3.95/1.71  Inferencing          : 0.19
% 3.95/1.71  Reduction            : 0.20
% 3.95/1.71  Demodulation         : 0.14
% 3.95/1.71  BG Simplification    : 0.03
% 3.95/1.71  Subsumption          : 0.11
% 3.95/1.71  Abstraction          : 0.04
% 3.95/1.71  MUC search           : 0.00
% 3.95/1.71  Cooper               : 0.00
% 3.95/1.71  Total                : 0.93
% 3.95/1.71  Index Insertion      : 0.00
% 3.95/1.71  Index Deletion       : 0.00
% 3.95/1.71  Index Matching       : 0.00
% 3.95/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
