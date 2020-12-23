%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:30 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 134 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  125 ( 366 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_1 > #skF_2

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

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_56,axiom,(
    ? [A] :
      ( l1_pre_topc(A)
      & v2_struct_0(A)
      & v1_pre_topc(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc11_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_49,plain,(
    ! [C_31,B_32,A_33] :
      ( v1_xboole_0(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(B_32,A_33)))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    ! [A_33] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_61,plain,(
    ! [A_33] : ~ v1_xboole_0(A_33) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_10,plain,(
    ! [A_10] :
      ( v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | ~ v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,(
    ! [A_37] :
      ( ~ l1_struct_0(A_37)
      | ~ v2_struct_0(A_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_10])).

tff(c_69,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_65])).

tff(c_77,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_69])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_77])).

tff(c_82,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_55,plain,(
    ! [B_34,A_35] :
      ( v2_tex_2(B_34,A_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ v1_xboole_0(B_34)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_60,plain,(
    ! [A_35] :
      ( v2_tex_2(k1_xboole_0,A_35)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_2,c_55])).

tff(c_84,plain,(
    ! [A_35] :
      ( v2_tex_2(k1_xboole_0,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_60])).

tff(c_98,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1('#skF_2'(A_47,B_48),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ v2_tex_2(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v3_tdlat_3(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [B_21] :
      ( ~ v3_tex_2(B_21,'#skF_3')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_111,plain,(
    ! [B_48] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_48),'#skF_3')
      | ~ v2_tex_2(B_48,'#skF_3')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_98,c_26])).

tff(c_118,plain,(
    ! [B_48] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_48),'#skF_3')
      | ~ v2_tex_2(B_48,'#skF_3')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_111])).

tff(c_120,plain,(
    ! [B_49] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_49),'#skF_3')
      | ~ v2_tex_2(B_49,'#skF_3')
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_118])).

tff(c_133,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',k1_xboole_0),'#skF_3')
    | ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_120])).

tff(c_135,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_138,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_135])).

tff(c_141,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_138])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_141])).

tff(c_145,plain,(
    v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_86,plain,(
    ! [A_41,B_42] :
      ( v3_tex_2('#skF_2'(A_41,B_42),A_41)
      | ~ v2_tex_2(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v3_tdlat_3(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_90,plain,(
    ! [A_41] :
      ( v3_tex_2('#skF_2'(A_41,k1_xboole_0),A_41)
      | ~ v2_tex_2(k1_xboole_0,A_41)
      | ~ l1_pre_topc(A_41)
      | ~ v3_tdlat_3(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_2,c_86])).

tff(c_144,plain,(
    ~ v3_tex_2('#skF_2'('#skF_3',k1_xboole_0),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_148,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_144])).

tff(c_151,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_145,c_148])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.25  
% 2.18/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.25  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_1 > #skF_2
% 2.18/1.25  
% 2.18/1.25  %Foreground sorts:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Background operators:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Foreground operators:
% 2.18/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.25  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.18/1.25  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.18/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.25  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.18/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.18/1.25  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.18/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.18/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.25  
% 2.18/1.27  tff(f_108, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.18/1.27  tff(f_56, axiom, (?[A]: ((l1_pre_topc(A) & v2_struct_0(A)) & v1_pre_topc(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc11_pre_topc)).
% 2.18/1.27  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.18/1.27  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.18/1.27  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.18/1.27  tff(f_50, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 2.18/1.27  tff(f_70, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.18/1.27  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.18/1.27  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.18/1.27  tff(c_32, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.18/1.27  tff(c_30, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.18/1.27  tff(c_28, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.18/1.27  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.18/1.27  tff(c_8, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.27  tff(c_14, plain, (v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.18/1.27  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.27  tff(c_49, plain, (![C_31, B_32, A_33]: (v1_xboole_0(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(B_32, A_33))) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.27  tff(c_54, plain, (![A_33]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_2, c_49])).
% 2.18/1.27  tff(c_61, plain, (![A_33]: (~v1_xboole_0(A_33))), inference(splitLeft, [status(thm)], [c_54])).
% 2.18/1.27  tff(c_10, plain, (![A_10]: (v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | ~v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.27  tff(c_65, plain, (![A_37]: (~l1_struct_0(A_37) | ~v2_struct_0(A_37))), inference(negUnitSimplification, [status(thm)], [c_61, c_10])).
% 2.18/1.27  tff(c_69, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_65])).
% 2.18/1.27  tff(c_77, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_69])).
% 2.18/1.27  tff(c_81, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_77])).
% 2.18/1.27  tff(c_82, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_54])).
% 2.18/1.27  tff(c_55, plain, (![B_34, A_35]: (v2_tex_2(B_34, A_35) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_35))) | ~v1_xboole_0(B_34) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.18/1.27  tff(c_60, plain, (![A_35]: (v2_tex_2(k1_xboole_0, A_35) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(resolution, [status(thm)], [c_2, c_55])).
% 2.18/1.27  tff(c_84, plain, (![A_35]: (v2_tex_2(k1_xboole_0, A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_60])).
% 2.18/1.27  tff(c_98, plain, (![A_47, B_48]: (m1_subset_1('#skF_2'(A_47, B_48), k1_zfmisc_1(u1_struct_0(A_47))) | ~v2_tex_2(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v3_tdlat_3(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.18/1.27  tff(c_26, plain, (![B_21]: (~v3_tex_2(B_21, '#skF_3') | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.18/1.27  tff(c_111, plain, (![B_48]: (~v3_tex_2('#skF_2'('#skF_3', B_48), '#skF_3') | ~v2_tex_2(B_48, '#skF_3') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_98, c_26])).
% 2.18/1.27  tff(c_118, plain, (![B_48]: (~v3_tex_2('#skF_2'('#skF_3', B_48), '#skF_3') | ~v2_tex_2(B_48, '#skF_3') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_111])).
% 2.18/1.27  tff(c_120, plain, (![B_49]: (~v3_tex_2('#skF_2'('#skF_3', B_49), '#skF_3') | ~v2_tex_2(B_49, '#skF_3') | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_118])).
% 2.18/1.27  tff(c_133, plain, (~v3_tex_2('#skF_2'('#skF_3', k1_xboole_0), '#skF_3') | ~v2_tex_2(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_2, c_120])).
% 2.18/1.27  tff(c_135, plain, (~v2_tex_2(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_133])).
% 2.18/1.27  tff(c_138, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_135])).
% 2.18/1.27  tff(c_141, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_138])).
% 2.18/1.27  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_141])).
% 2.18/1.27  tff(c_145, plain, (v2_tex_2(k1_xboole_0, '#skF_3')), inference(splitRight, [status(thm)], [c_133])).
% 2.18/1.27  tff(c_86, plain, (![A_41, B_42]: (v3_tex_2('#skF_2'(A_41, B_42), A_41) | ~v2_tex_2(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v3_tdlat_3(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.18/1.27  tff(c_90, plain, (![A_41]: (v3_tex_2('#skF_2'(A_41, k1_xboole_0), A_41) | ~v2_tex_2(k1_xboole_0, A_41) | ~l1_pre_topc(A_41) | ~v3_tdlat_3(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_2, c_86])).
% 2.18/1.27  tff(c_144, plain, (~v3_tex_2('#skF_2'('#skF_3', k1_xboole_0), '#skF_3')), inference(splitRight, [status(thm)], [c_133])).
% 2.18/1.27  tff(c_148, plain, (~v2_tex_2(k1_xboole_0, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_90, c_144])).
% 2.18/1.27  tff(c_151, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_145, c_148])).
% 2.18/1.27  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_151])).
% 2.18/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  Inference rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Ref     : 0
% 2.18/1.27  #Sup     : 18
% 2.18/1.27  #Fact    : 0
% 2.18/1.27  #Define  : 0
% 2.18/1.27  #Split   : 2
% 2.18/1.27  #Chain   : 0
% 2.18/1.27  #Close   : 0
% 2.18/1.27  
% 2.18/1.27  Ordering : KBO
% 2.18/1.27  
% 2.18/1.27  Simplification rules
% 2.18/1.27  ----------------------
% 2.18/1.27  #Subsume      : 2
% 2.18/1.27  #Demod        : 14
% 2.18/1.27  #Tautology    : 0
% 2.18/1.27  #SimpNegUnit  : 6
% 2.18/1.27  #BackRed      : 1
% 2.18/1.27  
% 2.18/1.27  #Partial instantiations: 0
% 2.18/1.27  #Strategies tried      : 1
% 2.18/1.27  
% 2.18/1.27  Timing (in seconds)
% 2.18/1.27  ----------------------
% 2.18/1.27  Preprocessing        : 0.27
% 2.18/1.27  Parsing              : 0.15
% 2.18/1.27  CNF conversion       : 0.02
% 2.18/1.27  Main loop            : 0.17
% 2.24/1.27  Inferencing          : 0.07
% 2.24/1.27  Reduction            : 0.04
% 2.24/1.27  Demodulation         : 0.03
% 2.24/1.27  BG Simplification    : 0.01
% 2.24/1.27  Subsumption          : 0.03
% 2.24/1.27  Abstraction          : 0.01
% 2.24/1.27  MUC search           : 0.00
% 2.24/1.27  Cooper               : 0.00
% 2.24/1.27  Total                : 0.48
% 2.24/1.27  Index Insertion      : 0.00
% 2.24/1.27  Index Deletion       : 0.00
% 2.24/1.27  Index Matching       : 0.00
% 2.24/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
