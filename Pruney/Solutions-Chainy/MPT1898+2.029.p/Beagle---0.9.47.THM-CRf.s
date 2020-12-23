%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:34 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 108 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 323 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_71,axiom,(
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

tff(c_24,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_36,plain,(
    ! [B_21,A_22] :
      ( v2_tex_2(B_21,A_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v1_xboole_0(B_21)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [A_22] :
      ( v2_tex_2(k1_xboole_0,A_22)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_4,c_36])).

tff(c_43,plain,(
    ! [A_22] :
      ( v2_tex_2(k1_xboole_0,A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_57,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1('#skF_1'(A_31,B_32),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ v2_tex_2(B_32,A_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v3_tdlat_3(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [B_15] :
      ( ~ v3_tex_2(B_15,'#skF_2')
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_70,plain,(
    ! [B_32] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_32),'#skF_2')
      | ~ v2_tex_2(B_32,'#skF_2')
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_57,c_16])).

tff(c_77,plain,(
    ! [B_32] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_32),'#skF_2')
      | ~ v2_tex_2(B_32,'#skF_2')
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_70])).

tff(c_79,plain,(
    ! [B_33] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_33),'#skF_2')
      | ~ v2_tex_2(B_33,'#skF_2')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_77])).

tff(c_92,plain,
    ( ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2')
    | ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_79])).

tff(c_93,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_96,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_93])).

tff(c_99,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_96])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_99])).

tff(c_103,plain,(
    v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_52,plain,(
    ! [A_29,B_30] :
      ( v3_tex_2('#skF_1'(A_29,B_30),A_29)
      | ~ v2_tex_2(B_30,A_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v3_tdlat_3(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_105,plain,(
    ! [A_35] :
      ( v3_tex_2('#skF_1'(A_35,k1_xboole_0),A_35)
      | ~ v2_tex_2(k1_xboole_0,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v3_tdlat_3(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_102,plain,(
    ~ v3_tex_2('#skF_1'('#skF_2',k1_xboole_0),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_108,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_105,c_102])).

tff(c_111,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_103,c_108])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.08/1.25  
% 2.08/1.25  %Foreground sorts:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Background operators:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Foreground operators:
% 2.08/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.08/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.25  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.08/1.25  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.08/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.25  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.08/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.25  
% 2.08/1.27  tff(f_86, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.08/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.08/1.27  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.08/1.27  tff(f_48, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.08/1.27  tff(f_71, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.08/1.27  tff(c_24, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.08/1.27  tff(c_22, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.08/1.27  tff(c_20, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.08/1.27  tff(c_18, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.08/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.08/1.27  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.08/1.27  tff(c_36, plain, (![B_21, A_22]: (v2_tex_2(B_21, A_22) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_22))) | ~v1_xboole_0(B_21) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.27  tff(c_40, plain, (![A_22]: (v2_tex_2(k1_xboole_0, A_22) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_4, c_36])).
% 2.08/1.27  tff(c_43, plain, (![A_22]: (v2_tex_2(k1_xboole_0, A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 2.08/1.27  tff(c_57, plain, (![A_31, B_32]: (m1_subset_1('#skF_1'(A_31, B_32), k1_zfmisc_1(u1_struct_0(A_31))) | ~v2_tex_2(B_32, A_31) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v3_tdlat_3(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.08/1.27  tff(c_16, plain, (![B_15]: (~v3_tex_2(B_15, '#skF_2') | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.08/1.27  tff(c_70, plain, (![B_32]: (~v3_tex_2('#skF_1'('#skF_2', B_32), '#skF_2') | ~v2_tex_2(B_32, '#skF_2') | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_57, c_16])).
% 2.08/1.27  tff(c_77, plain, (![B_32]: (~v3_tex_2('#skF_1'('#skF_2', B_32), '#skF_2') | ~v2_tex_2(B_32, '#skF_2') | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_70])).
% 2.08/1.27  tff(c_79, plain, (![B_33]: (~v3_tex_2('#skF_1'('#skF_2', B_33), '#skF_2') | ~v2_tex_2(B_33, '#skF_2') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_24, c_77])).
% 2.08/1.27  tff(c_92, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2') | ~v2_tex_2(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_4, c_79])).
% 2.08/1.27  tff(c_93, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_92])).
% 2.08/1.27  tff(c_96, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_43, c_93])).
% 2.08/1.27  tff(c_99, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_96])).
% 2.08/1.27  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_99])).
% 2.08/1.27  tff(c_103, plain, (v2_tex_2(k1_xboole_0, '#skF_2')), inference(splitRight, [status(thm)], [c_92])).
% 2.08/1.27  tff(c_52, plain, (![A_29, B_30]: (v3_tex_2('#skF_1'(A_29, B_30), A_29) | ~v2_tex_2(B_30, A_29) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v3_tdlat_3(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.08/1.27  tff(c_105, plain, (![A_35]: (v3_tex_2('#skF_1'(A_35, k1_xboole_0), A_35) | ~v2_tex_2(k1_xboole_0, A_35) | ~l1_pre_topc(A_35) | ~v3_tdlat_3(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(resolution, [status(thm)], [c_4, c_52])).
% 2.08/1.27  tff(c_102, plain, (~v3_tex_2('#skF_1'('#skF_2', k1_xboole_0), '#skF_2')), inference(splitRight, [status(thm)], [c_92])).
% 2.08/1.27  tff(c_108, plain, (~v2_tex_2(k1_xboole_0, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_105, c_102])).
% 2.08/1.27  tff(c_111, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_103, c_108])).
% 2.08/1.27  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_111])).
% 2.08/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  Inference rules
% 2.08/1.27  ----------------------
% 2.08/1.27  #Ref     : 0
% 2.08/1.27  #Sup     : 14
% 2.08/1.27  #Fact    : 0
% 2.08/1.27  #Define  : 0
% 2.08/1.27  #Split   : 1
% 2.08/1.27  #Chain   : 0
% 2.08/1.27  #Close   : 0
% 2.08/1.27  
% 2.08/1.27  Ordering : KBO
% 2.08/1.27  
% 2.08/1.27  Simplification rules
% 2.08/1.27  ----------------------
% 2.08/1.27  #Subsume      : 0
% 2.08/1.27  #Demod        : 13
% 2.08/1.27  #Tautology    : 0
% 2.08/1.27  #SimpNegUnit  : 4
% 2.08/1.27  #BackRed      : 0
% 2.08/1.27  
% 2.08/1.27  #Partial instantiations: 0
% 2.08/1.27  #Strategies tried      : 1
% 2.08/1.27  
% 2.08/1.27  Timing (in seconds)
% 2.08/1.27  ----------------------
% 2.08/1.27  Preprocessing        : 0.27
% 2.08/1.27  Parsing              : 0.15
% 2.08/1.27  CNF conversion       : 0.02
% 2.08/1.27  Main loop            : 0.16
% 2.08/1.27  Inferencing          : 0.07
% 2.08/1.27  Reduction            : 0.04
% 2.08/1.27  Demodulation         : 0.03
% 2.08/1.27  BG Simplification    : 0.01
% 2.08/1.27  Subsumption          : 0.03
% 2.08/1.27  Abstraction          : 0.01
% 2.08/1.27  MUC search           : 0.00
% 2.08/1.27  Cooper               : 0.00
% 2.08/1.27  Total                : 0.45
% 2.08/1.27  Index Insertion      : 0.00
% 2.08/1.27  Index Deletion       : 0.00
% 2.08/1.27  Index Matching       : 0.00
% 2.08/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
