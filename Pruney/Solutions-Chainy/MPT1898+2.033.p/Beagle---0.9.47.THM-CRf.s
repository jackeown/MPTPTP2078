%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:34 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 107 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 329 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_30,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_67,axiom,(
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

tff(c_22,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1] : v1_xboole_0('#skF_1'(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_31,plain,(
    ! [B_17,A_18] :
      ( v2_tex_2(B_17,A_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ v1_xboole_0(B_17)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_35,plain,(
    ! [A_18] :
      ( v2_tex_2('#skF_1'(u1_struct_0(A_18)),A_18)
      | ~ v1_xboole_0('#skF_1'(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_4,c_31])).

tff(c_38,plain,(
    ! [A_18] :
      ( v2_tex_2('#skF_1'(u1_struct_0(A_18)),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_35])).

tff(c_52,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1('#skF_2'(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ v2_tex_2(B_27,A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v3_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [B_13] :
      ( ~ v3_tex_2(B_13,'#skF_3')
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_63,plain,(
    ! [B_27] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_27),'#skF_3')
      | ~ v2_tex_2(B_27,'#skF_3')
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_14])).

tff(c_69,plain,(
    ! [B_27] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_27),'#skF_3')
      | ~ v2_tex_2(B_27,'#skF_3')
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_63])).

tff(c_71,plain,(
    ! [B_28] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_28),'#skF_3')
      | ~ v2_tex_2(B_28,'#skF_3')
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_69])).

tff(c_84,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3','#skF_1'(u1_struct_0('#skF_3'))),'#skF_3')
    | ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_85,plain,(
    ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_88,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_85])).

tff(c_91,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_88])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_91])).

tff(c_95,plain,(
    v2_tex_2('#skF_1'(u1_struct_0('#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_45,plain,(
    ! [A_22,B_23] :
      ( v3_tex_2('#skF_2'(A_22,B_23),A_22)
      | ~ v2_tex_2(B_23,A_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v3_tdlat_3(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_49,plain,(
    ! [A_22] :
      ( v3_tex_2('#skF_2'(A_22,'#skF_1'(u1_struct_0(A_22))),A_22)
      | ~ v2_tex_2('#skF_1'(u1_struct_0(A_22)),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v3_tdlat_3(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_4,c_45])).

tff(c_94,plain,(
    ~ v3_tex_2('#skF_2'('#skF_3','#skF_1'(u1_struct_0('#skF_3'))),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_99,plain,
    ( ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_3')),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_49,c_94])).

tff(c_102,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_95,c_99])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:49:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.16  
% 1.77/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.16  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2
% 1.87/1.16  
% 1.87/1.16  %Foreground sorts:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Background operators:
% 1.87/1.16  
% 1.87/1.16  
% 1.87/1.16  %Foreground operators:
% 1.87/1.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.87/1.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.87/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.16  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.87/1.16  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.87/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.16  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.87/1.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.87/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.16  
% 1.87/1.18  tff(f_82, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 1.87/1.18  tff(f_30, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 1.87/1.18  tff(f_44, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 1.87/1.18  tff(f_67, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 1.87/1.18  tff(c_22, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.87/1.18  tff(c_20, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.87/1.18  tff(c_18, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.87/1.18  tff(c_16, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.87/1.18  tff(c_2, plain, (![A_1]: (v1_xboole_0('#skF_1'(A_1)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.87/1.18  tff(c_4, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.87/1.18  tff(c_31, plain, (![B_17, A_18]: (v2_tex_2(B_17, A_18) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_18))) | ~v1_xboole_0(B_17) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.87/1.18  tff(c_35, plain, (![A_18]: (v2_tex_2('#skF_1'(u1_struct_0(A_18)), A_18) | ~v1_xboole_0('#skF_1'(u1_struct_0(A_18))) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(resolution, [status(thm)], [c_4, c_31])).
% 1.87/1.18  tff(c_38, plain, (![A_18]: (v2_tex_2('#skF_1'(u1_struct_0(A_18)), A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_35])).
% 1.87/1.18  tff(c_52, plain, (![A_26, B_27]: (m1_subset_1('#skF_2'(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~v2_tex_2(B_27, A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v3_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.18  tff(c_14, plain, (![B_13]: (~v3_tex_2(B_13, '#skF_3') | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.87/1.18  tff(c_63, plain, (![B_27]: (~v3_tex_2('#skF_2'('#skF_3', B_27), '#skF_3') | ~v2_tex_2(B_27, '#skF_3') | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_14])).
% 1.87/1.18  tff(c_69, plain, (![B_27]: (~v3_tex_2('#skF_2'('#skF_3', B_27), '#skF_3') | ~v2_tex_2(B_27, '#skF_3') | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_63])).
% 1.87/1.18  tff(c_71, plain, (![B_28]: (~v3_tex_2('#skF_2'('#skF_3', B_28), '#skF_3') | ~v2_tex_2(B_28, '#skF_3') | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_22, c_69])).
% 1.87/1.18  tff(c_84, plain, (~v3_tex_2('#skF_2'('#skF_3', '#skF_1'(u1_struct_0('#skF_3'))), '#skF_3') | ~v2_tex_2('#skF_1'(u1_struct_0('#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_4, c_71])).
% 1.87/1.18  tff(c_85, plain, (~v2_tex_2('#skF_1'(u1_struct_0('#skF_3')), '#skF_3')), inference(splitLeft, [status(thm)], [c_84])).
% 1.87/1.18  tff(c_88, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_85])).
% 1.87/1.18  tff(c_91, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_88])).
% 1.87/1.18  tff(c_93, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_91])).
% 1.87/1.18  tff(c_95, plain, (v2_tex_2('#skF_1'(u1_struct_0('#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_84])).
% 1.87/1.18  tff(c_45, plain, (![A_22, B_23]: (v3_tex_2('#skF_2'(A_22, B_23), A_22) | ~v2_tex_2(B_23, A_22) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22) | ~v3_tdlat_3(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.18  tff(c_49, plain, (![A_22]: (v3_tex_2('#skF_2'(A_22, '#skF_1'(u1_struct_0(A_22))), A_22) | ~v2_tex_2('#skF_1'(u1_struct_0(A_22)), A_22) | ~l1_pre_topc(A_22) | ~v3_tdlat_3(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_4, c_45])).
% 1.87/1.18  tff(c_94, plain, (~v3_tex_2('#skF_2'('#skF_3', '#skF_1'(u1_struct_0('#skF_3'))), '#skF_3')), inference(splitRight, [status(thm)], [c_84])).
% 1.87/1.18  tff(c_99, plain, (~v2_tex_2('#skF_1'(u1_struct_0('#skF_3')), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_49, c_94])).
% 1.87/1.18  tff(c_102, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_95, c_99])).
% 1.87/1.18  tff(c_104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_102])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 12
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 1
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 0
% 1.87/1.18  #Demod        : 13
% 1.87/1.18  #Tautology    : 0
% 1.87/1.18  #SimpNegUnit  : 4
% 1.87/1.18  #BackRed      : 0
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.87/1.18  Preprocessing        : 0.26
% 1.87/1.18  Parsing              : 0.15
% 1.87/1.18  CNF conversion       : 0.02
% 1.87/1.18  Main loop            : 0.15
% 1.87/1.18  Inferencing          : 0.07
% 1.87/1.18  Reduction            : 0.04
% 1.87/1.18  Demodulation         : 0.03
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.03
% 1.87/1.18  Abstraction          : 0.01
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.44
% 1.87/1.18  Index Insertion      : 0.00
% 1.87/1.18  Index Deletion       : 0.00
% 1.87/1.18  Index Matching       : 0.00
% 1.87/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
