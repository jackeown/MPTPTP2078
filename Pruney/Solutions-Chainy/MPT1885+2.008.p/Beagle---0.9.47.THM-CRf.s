%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:20 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 115 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  113 ( 400 expanded)
%              Number of equality atoms :    8 (  40 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ ( v3_tex_2(B,A)
                & ! [C] :
                    ( ( ~ v2_struct_0(C)
                      & v1_pre_topc(C)
                      & m1_pre_topc(C,A) )
                   => ~ ( v4_tex_2(C,A)
                        & B = u1_struct_0(C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v3_tex_2(C,A)
                <=> v4_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_61,plain,(
    ! [A_39,B_40] :
      ( m1_pre_topc(k1_pre_topc(A_39,B_40),A_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_69,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_65])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( l1_pre_topc(B_6)
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_8])).

tff(c_100,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_97])).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_50,plain,(
    ! [A_37,B_38] :
      ( u1_struct_0(k1_pre_topc(A_37,B_38)) = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_60,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | ~ v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_90,plain,
    ( v1_xboole_0('#skF_2')
    | ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_10])).

tff(c_93,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_90])).

tff(c_101,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_22,plain,(
    v3_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    ! [A_33,B_34] :
      ( v1_pre_topc(k1_pre_topc(A_33,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_38])).

tff(c_48,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_44])).

tff(c_14,plain,(
    ! [B_13,A_11] :
      ( m1_subset_1(u1_struct_0(B_13),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_128,plain,(
    ! [B_47,A_48] :
      ( v4_tex_2(B_47,A_48)
      | ~ v3_tex_2(u1_struct_0(B_47),A_48)
      | ~ m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_228,plain,(
    ! [B_54,A_55] :
      ( v4_tex_2(B_54,A_55)
      | ~ v3_tex_2(u1_struct_0(B_54),A_55)
      | v2_struct_0(A_55)
      | ~ m1_pre_topc(B_54,A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_14,c_128])).

tff(c_346,plain,(
    ! [A_64] :
      ( v4_tex_2(k1_pre_topc('#skF_1','#skF_2'),A_64)
      | ~ v3_tex_2('#skF_2',A_64)
      | v2_struct_0(A_64)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_228])).

tff(c_20,plain,(
    ! [C_25] :
      ( u1_struct_0(C_25) != '#skF_2'
      | ~ v4_tex_2(C_25,'#skF_1')
      | ~ m1_pre_topc(C_25,'#skF_1')
      | ~ v1_pre_topc(C_25)
      | v2_struct_0(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_353,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) != '#skF_2'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v3_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_346,c_20])).

tff(c_357,plain,
    ( v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_69,c_22,c_48,c_60,c_353])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_101,c_357])).

tff(c_360,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_364,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_360])).

tff(c_368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:51:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.35  %$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.47/1.35  
% 2.47/1.35  %Foreground sorts:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Background operators:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Foreground operators:
% 2.47/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.47/1.35  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.35  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.47/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.47/1.35  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.47/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.35  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.47/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.47/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.47/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.35  
% 2.47/1.36  tff(f_111, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v3_tex_2(B, A) & (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ~(v4_tex_2(C, A) & (B = u1_struct_0(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tex_2)).
% 2.47/1.36  tff(f_33, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 2.47/1.36  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.47/1.36  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.47/1.36  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.47/1.36  tff(f_50, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 2.47/1.36  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.47/1.36  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v3_tex_2(C, A) <=> v4_tex_2(B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_tex_2)).
% 2.47/1.36  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.47/1.36  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.47/1.36  tff(c_61, plain, (![A_39, B_40]: (m1_pre_topc(k1_pre_topc(A_39, B_40), A_39) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.36  tff(c_65, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_61])).
% 2.47/1.36  tff(c_69, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_65])).
% 2.47/1.36  tff(c_8, plain, (![B_6, A_4]: (l1_pre_topc(B_6) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.47/1.36  tff(c_97, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_8])).
% 2.47/1.36  tff(c_100, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_97])).
% 2.47/1.36  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.36  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.47/1.36  tff(c_26, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.47/1.36  tff(c_50, plain, (![A_37, B_38]: (u1_struct_0(k1_pre_topc(A_37, B_38))=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.47/1.36  tff(c_56, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_50])).
% 2.47/1.36  tff(c_60, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_56])).
% 2.47/1.36  tff(c_10, plain, (![A_7]: (v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | ~v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.47/1.36  tff(c_90, plain, (v1_xboole_0('#skF_2') | ~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_10])).
% 2.47/1.36  tff(c_93, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_90])).
% 2.47/1.36  tff(c_101, plain, (~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_93])).
% 2.47/1.36  tff(c_22, plain, (v3_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.47/1.36  tff(c_38, plain, (![A_33, B_34]: (v1_pre_topc(k1_pre_topc(A_33, B_34)) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.36  tff(c_44, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_38])).
% 2.47/1.36  tff(c_48, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_44])).
% 2.47/1.36  tff(c_14, plain, (![B_13, A_11]: (m1_subset_1(u1_struct_0(B_13), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.36  tff(c_128, plain, (![B_47, A_48]: (v4_tex_2(B_47, A_48) | ~v3_tex_2(u1_struct_0(B_47), A_48) | ~m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.47/1.36  tff(c_228, plain, (![B_54, A_55]: (v4_tex_2(B_54, A_55) | ~v3_tex_2(u1_struct_0(B_54), A_55) | v2_struct_0(A_55) | ~m1_pre_topc(B_54, A_55) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_14, c_128])).
% 2.47/1.36  tff(c_346, plain, (![A_64]: (v4_tex_2(k1_pre_topc('#skF_1', '#skF_2'), A_64) | ~v3_tex_2('#skF_2', A_64) | v2_struct_0(A_64) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_64) | ~l1_pre_topc(A_64))), inference(superposition, [status(thm), theory('equality')], [c_60, c_228])).
% 2.47/1.36  tff(c_20, plain, (![C_25]: (u1_struct_0(C_25)!='#skF_2' | ~v4_tex_2(C_25, '#skF_1') | ~m1_pre_topc(C_25, '#skF_1') | ~v1_pre_topc(C_25) | v2_struct_0(C_25))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.47/1.36  tff(c_353, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))!='#skF_2' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v3_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_346, c_20])).
% 2.47/1.36  tff(c_357, plain, (v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_69, c_22, c_48, c_60, c_353])).
% 2.47/1.36  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_101, c_357])).
% 2.47/1.36  tff(c_360, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_93])).
% 2.47/1.36  tff(c_364, plain, (~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_360])).
% 2.47/1.36  tff(c_368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_364])).
% 2.47/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  Inference rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Ref     : 0
% 2.47/1.36  #Sup     : 80
% 2.47/1.36  #Fact    : 0
% 2.47/1.36  #Define  : 0
% 2.47/1.36  #Split   : 2
% 2.47/1.36  #Chain   : 0
% 2.47/1.36  #Close   : 0
% 2.47/1.36  
% 2.47/1.36  Ordering : KBO
% 2.47/1.36  
% 2.47/1.36  Simplification rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Subsume      : 6
% 2.47/1.36  #Demod        : 29
% 2.47/1.36  #Tautology    : 15
% 2.47/1.36  #SimpNegUnit  : 4
% 2.47/1.36  #BackRed      : 0
% 2.47/1.36  
% 2.47/1.36  #Partial instantiations: 0
% 2.47/1.36  #Strategies tried      : 1
% 2.47/1.36  
% 2.47/1.36  Timing (in seconds)
% 2.47/1.36  ----------------------
% 2.47/1.37  Preprocessing        : 0.31
% 2.47/1.37  Parsing              : 0.18
% 2.47/1.37  CNF conversion       : 0.02
% 2.47/1.37  Main loop            : 0.26
% 2.47/1.37  Inferencing          : 0.10
% 2.47/1.37  Reduction            : 0.07
% 2.47/1.37  Demodulation         : 0.05
% 2.47/1.37  BG Simplification    : 0.02
% 2.47/1.37  Subsumption          : 0.06
% 2.47/1.37  Abstraction          : 0.01
% 2.47/1.37  MUC search           : 0.00
% 2.47/1.37  Cooper               : 0.00
% 2.47/1.37  Total                : 0.60
% 2.47/1.37  Index Insertion      : 0.00
% 2.47/1.37  Index Deletion       : 0.00
% 2.47/1.37  Index Matching       : 0.00
% 2.47/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
