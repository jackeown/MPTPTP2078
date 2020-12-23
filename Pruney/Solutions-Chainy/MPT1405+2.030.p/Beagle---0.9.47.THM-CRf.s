%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:34 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 104 expanded)
%              Number of leaves         :   27 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :  123 ( 273 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

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

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_22,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_11] :
      ( m1_subset_1(k2_struct_0(A_11),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_72,plain,(
    ! [B_47,A_48,C_49] :
      ( r1_tarski(B_47,k1_tops_1(A_48,C_49))
      | ~ m2_connsp_2(C_49,A_48,B_47)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_79,plain,(
    ! [B_47] :
      ( r1_tarski(B_47,k1_tops_1('#skF_1','#skF_2'))
      | ~ m2_connsp_2('#skF_2','#skF_1',B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_72])).

tff(c_85,plain,(
    ! [B_50] :
      ( r1_tarski(B_50,k1_tops_1('#skF_1','#skF_2'))
      | ~ m2_connsp_2('#skF_2','#skF_1',B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_79])).

tff(c_98,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))
    | ~ m2_connsp_2('#skF_2','#skF_1',k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_101,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_104,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_104])).

tff(c_110,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_16,plain,(
    ! [A_16] :
      ( k1_tops_1(A_16,k2_struct_0(A_16)) = k2_struct_0(A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_69,plain,(
    ! [C_44,A_45,B_46] :
      ( m2_connsp_2(C_44,A_45,B_46)
      | ~ r1_tarski(B_46,k1_tops_1(A_45,C_44))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_126,plain,(
    ! [A_56,B_57] :
      ( m2_connsp_2(k2_struct_0(A_56),A_56,B_57)
      | ~ r1_tarski(B_57,k2_struct_0(A_56))
      | ~ m1_subset_1(k2_struct_0(A_56),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_69])).

tff(c_130,plain,(
    ! [A_58,B_59] :
      ( m2_connsp_2(k2_struct_0(A_58),A_58,B_59)
      | ~ r1_tarski(B_59,k2_struct_0(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | ~ l1_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_137,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_130])).

tff(c_142,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_28,c_26,c_137])).

tff(c_143,plain,(
    ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_142])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_13,B_15] :
      ( k4_subset_1(u1_struct_0(A_13),B_15,k3_subset_1(u1_struct_0(A_13),B_15)) = k2_struct_0(A_13)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_tarski(k3_subset_1(A_32,k4_subset_1(A_32,B_33,C_34)),k3_subset_1(A_32,B_33))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_156,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k3_subset_1(u1_struct_0(A_66),k2_struct_0(A_66)),k3_subset_1(u1_struct_0(A_66),B_67))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_66),B_67),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_struct_0(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_52])).

tff(c_4,plain,(
    ! [B_4,C_6,A_3] :
      ( r1_tarski(B_4,C_6)
      | ~ r1_tarski(k3_subset_1(A_3,C_6),k3_subset_1(A_3,B_4))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_161,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(B_68,k2_struct_0(A_69))
      | ~ m1_subset_1(k2_struct_0(A_69),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_69),B_68),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_156,c_4])).

tff(c_171,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(B_72,k2_struct_0(A_73))
      | ~ m1_subset_1(k2_struct_0(A_73),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_struct_0(A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73))) ) ),
    inference(resolution,[status(thm)],[c_2,c_161])).

tff(c_175,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(B_74,k2_struct_0(A_75))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_struct_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_10,c_171])).

tff(c_185,plain,
    ( r1_tarski('#skF_2',k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_175])).

tff(c_190,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_185])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.24  
% 2.23/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.24  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.23/1.24  
% 2.23/1.24  %Foreground sorts:
% 2.23/1.24  
% 2.23/1.24  
% 2.23/1.24  %Background operators:
% 2.23/1.24  
% 2.23/1.24  
% 2.23/1.24  %Foreground operators:
% 2.23/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.23/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.23/1.24  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.23/1.24  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.23/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.23/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.24  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.23/1.24  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.23/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.24  
% 2.23/1.26  tff(f_93, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.23/1.26  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.23/1.26  tff(f_49, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.23/1.26  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.23/1.26  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.23/1.26  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.23/1.26  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_pre_topc)).
% 2.23/1.26  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 2.23/1.26  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.23/1.26  tff(c_22, plain, (~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.26  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.26  tff(c_12, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.26  tff(c_10, plain, (![A_11]: (m1_subset_1(k2_struct_0(A_11), k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.26  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.26  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.26  tff(c_72, plain, (![B_47, A_48, C_49]: (r1_tarski(B_47, k1_tops_1(A_48, C_49)) | ~m2_connsp_2(C_49, A_48, B_47) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.23/1.26  tff(c_79, plain, (![B_47]: (r1_tarski(B_47, k1_tops_1('#skF_1', '#skF_2')) | ~m2_connsp_2('#skF_2', '#skF_1', B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_72])).
% 2.23/1.26  tff(c_85, plain, (![B_50]: (r1_tarski(B_50, k1_tops_1('#skF_1', '#skF_2')) | ~m2_connsp_2('#skF_2', '#skF_1', B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_79])).
% 2.23/1.26  tff(c_98, plain, (r1_tarski(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')) | ~m2_connsp_2('#skF_2', '#skF_1', k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_85])).
% 2.23/1.26  tff(c_101, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_98])).
% 2.23/1.26  tff(c_104, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_101])).
% 2.23/1.26  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_104])).
% 2.23/1.26  tff(c_110, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_98])).
% 2.23/1.26  tff(c_16, plain, (![A_16]: (k1_tops_1(A_16, k2_struct_0(A_16))=k2_struct_0(A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.26  tff(c_69, plain, (![C_44, A_45, B_46]: (m2_connsp_2(C_44, A_45, B_46) | ~r1_tarski(B_46, k1_tops_1(A_45, C_44)) | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.23/1.26  tff(c_126, plain, (![A_56, B_57]: (m2_connsp_2(k2_struct_0(A_56), A_56, B_57) | ~r1_tarski(B_57, k2_struct_0(A_56)) | ~m1_subset_1(k2_struct_0(A_56), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56))), inference(superposition, [status(thm), theory('equality')], [c_16, c_69])).
% 2.23/1.26  tff(c_130, plain, (![A_58, B_59]: (m2_connsp_2(k2_struct_0(A_58), A_58, B_59) | ~r1_tarski(B_59, k2_struct_0(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | ~l1_struct_0(A_58))), inference(resolution, [status(thm)], [c_10, c_126])).
% 2.23/1.26  tff(c_137, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_130])).
% 2.23/1.26  tff(c_142, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_28, c_26, c_137])).
% 2.23/1.26  tff(c_143, plain, (~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_22, c_142])).
% 2.23/1.26  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.26  tff(c_14, plain, (![A_13, B_15]: (k4_subset_1(u1_struct_0(A_13), B_15, k3_subset_1(u1_struct_0(A_13), B_15))=k2_struct_0(A_13) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.26  tff(c_52, plain, (![A_32, B_33, C_34]: (r1_tarski(k3_subset_1(A_32, k4_subset_1(A_32, B_33, C_34)), k3_subset_1(A_32, B_33)) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.26  tff(c_156, plain, (![A_66, B_67]: (r1_tarski(k3_subset_1(u1_struct_0(A_66), k2_struct_0(A_66)), k3_subset_1(u1_struct_0(A_66), B_67)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_66), B_67), k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_struct_0(A_66))), inference(superposition, [status(thm), theory('equality')], [c_14, c_52])).
% 2.23/1.26  tff(c_4, plain, (![B_4, C_6, A_3]: (r1_tarski(B_4, C_6) | ~r1_tarski(k3_subset_1(A_3, C_6), k3_subset_1(A_3, B_4)) | ~m1_subset_1(C_6, k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.23/1.26  tff(c_161, plain, (![B_68, A_69]: (r1_tarski(B_68, k2_struct_0(A_69)) | ~m1_subset_1(k2_struct_0(A_69), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_69), B_68), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_struct_0(A_69))), inference(resolution, [status(thm)], [c_156, c_4])).
% 2.23/1.26  tff(c_171, plain, (![B_72, A_73]: (r1_tarski(B_72, k2_struct_0(A_73)) | ~m1_subset_1(k2_struct_0(A_73), k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_struct_0(A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))))), inference(resolution, [status(thm)], [c_2, c_161])).
% 2.23/1.26  tff(c_175, plain, (![B_74, A_75]: (r1_tarski(B_74, k2_struct_0(A_75)) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_struct_0(A_75))), inference(resolution, [status(thm)], [c_10, c_171])).
% 2.23/1.26  tff(c_185, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_175])).
% 2.23/1.26  tff(c_190, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_185])).
% 2.23/1.26  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_190])).
% 2.23/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.26  
% 2.23/1.26  Inference rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Ref     : 0
% 2.23/1.26  #Sup     : 33
% 2.23/1.26  #Fact    : 0
% 2.23/1.26  #Define  : 0
% 2.23/1.26  #Split   : 3
% 2.23/1.26  #Chain   : 0
% 2.23/1.26  #Close   : 0
% 2.23/1.26  
% 2.23/1.26  Ordering : KBO
% 2.23/1.26  
% 2.23/1.26  Simplification rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Subsume      : 4
% 2.34/1.26  #Demod        : 10
% 2.34/1.26  #Tautology    : 10
% 2.34/1.26  #SimpNegUnit  : 2
% 2.34/1.26  #BackRed      : 0
% 2.34/1.26  
% 2.34/1.26  #Partial instantiations: 0
% 2.34/1.26  #Strategies tried      : 1
% 2.34/1.26  
% 2.34/1.26  Timing (in seconds)
% 2.34/1.26  ----------------------
% 2.34/1.26  Preprocessing        : 0.28
% 2.34/1.26  Parsing              : 0.16
% 2.34/1.26  CNF conversion       : 0.02
% 2.34/1.26  Main loop            : 0.22
% 2.34/1.26  Inferencing          : 0.09
% 2.34/1.26  Reduction            : 0.05
% 2.34/1.26  Demodulation         : 0.04
% 2.34/1.26  BG Simplification    : 0.01
% 2.34/1.26  Subsumption          : 0.04
% 2.34/1.26  Abstraction          : 0.01
% 2.34/1.26  MUC search           : 0.00
% 2.34/1.26  Cooper               : 0.00
% 2.34/1.26  Total                : 0.53
% 2.34/1.26  Index Insertion      : 0.00
% 2.34/1.26  Index Deletion       : 0.00
% 2.34/1.26  Index Matching       : 0.00
% 2.34/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
