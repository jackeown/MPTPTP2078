%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:34 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   49 (  74 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 203 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_69,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [B_22,A_23] :
      ( v2_tex_2(B_22,A_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ v1_xboole_0(B_22)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,(
    ! [A_24,A_25] :
      ( v2_tex_2(A_24,A_25)
      | ~ v1_xboole_0(A_24)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25)
      | ~ r1_tarski(A_24,u1_struct_0(A_25)) ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_56,plain,(
    ! [A_25] :
      ( v2_tex_2(k1_xboole_0,A_25)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_59,plain,(
    ! [A_25] :
      ( v2_tex_2(k1_xboole_0,A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_22,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_61,plain,(
    ! [A_27,B_28] :
      ( v3_tex_2('#skF_1'(A_27,B_28),A_27)
      | ~ v2_tex_2(B_28,A_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v3_tdlat_3(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_65,plain,(
    ! [A_27,A_2] :
      ( v3_tex_2('#skF_1'(A_27,A_2),A_27)
      | ~ v2_tex_2(A_2,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v3_tdlat_3(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27)
      | ~ r1_tarski(A_2,u1_struct_0(A_27)) ) ),
    inference(resolution,[status(thm)],[c_8,c_61])).

tff(c_78,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1('#skF_1'(A_35,B_36),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ v2_tex_2(B_36,A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v3_tdlat_3(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [B_14] :
      ( ~ v3_tex_2(B_14,'#skF_2')
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_89,plain,(
    ! [B_36] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_36),'#skF_2')
      | ~ v2_tex_2(B_36,'#skF_2')
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_78,c_18])).

tff(c_98,plain,(
    ! [B_36] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_36),'#skF_2')
      | ~ v2_tex_2(B_36,'#skF_2')
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_89])).

tff(c_101,plain,(
    ! [B_37] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',B_37),'#skF_2')
      | ~ v2_tex_2(B_37,'#skF_2')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_98])).

tff(c_115,plain,(
    ! [A_38] :
      ( ~ v3_tex_2('#skF_1'('#skF_2',A_38),'#skF_2')
      | ~ v2_tex_2(A_38,'#skF_2')
      | ~ r1_tarski(A_38,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_119,plain,(
    ! [A_2] :
      ( ~ v2_tex_2(A_2,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_2,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_65,c_115])).

tff(c_122,plain,(
    ! [A_2] :
      ( ~ v2_tex_2(A_2,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_2,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_119])).

tff(c_124,plain,(
    ! [A_39] :
      ( ~ v2_tex_2(A_39,'#skF_2')
      | ~ r1_tarski(A_39,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_122])).

tff(c_129,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_124])).

tff(c_132,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_59,c_129])).

tff(c_135,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:06:27 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.15  
% 1.88/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.15  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.88/1.15  
% 1.88/1.15  %Foreground sorts:
% 1.88/1.15  
% 1.88/1.15  
% 1.88/1.15  %Background operators:
% 1.88/1.15  
% 1.88/1.15  
% 1.88/1.15  %Foreground operators:
% 1.88/1.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.88/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.88/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.15  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.88/1.15  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.88/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.15  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 1.88/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.15  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.88/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.88/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.15  
% 1.88/1.17  tff(f_84, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 1.88/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.88/1.17  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.88/1.17  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.88/1.17  tff(f_46, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 1.88/1.17  tff(f_69, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 1.88/1.17  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.88/1.17  tff(c_24, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.88/1.17  tff(c_20, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.88/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.88/1.17  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.88/1.17  tff(c_8, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.17  tff(c_46, plain, (![B_22, A_23]: (v2_tex_2(B_22, A_23) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_23))) | ~v1_xboole_0(B_22) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.17  tff(c_52, plain, (![A_24, A_25]: (v2_tex_2(A_24, A_25) | ~v1_xboole_0(A_24) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25) | ~r1_tarski(A_24, u1_struct_0(A_25)))), inference(resolution, [status(thm)], [c_8, c_46])).
% 1.88/1.17  tff(c_56, plain, (![A_25]: (v2_tex_2(k1_xboole_0, A_25) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_4, c_52])).
% 1.88/1.17  tff(c_59, plain, (![A_25]: (v2_tex_2(k1_xboole_0, A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 1.88/1.17  tff(c_22, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.88/1.17  tff(c_61, plain, (![A_27, B_28]: (v3_tex_2('#skF_1'(A_27, B_28), A_27) | ~v2_tex_2(B_28, A_27) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27) | ~v3_tdlat_3(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.88/1.17  tff(c_65, plain, (![A_27, A_2]: (v3_tex_2('#skF_1'(A_27, A_2), A_27) | ~v2_tex_2(A_2, A_27) | ~l1_pre_topc(A_27) | ~v3_tdlat_3(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27) | ~r1_tarski(A_2, u1_struct_0(A_27)))), inference(resolution, [status(thm)], [c_8, c_61])).
% 1.88/1.17  tff(c_78, plain, (![A_35, B_36]: (m1_subset_1('#skF_1'(A_35, B_36), k1_zfmisc_1(u1_struct_0(A_35))) | ~v2_tex_2(B_36, A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v3_tdlat_3(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.88/1.17  tff(c_18, plain, (![B_14]: (~v3_tex_2(B_14, '#skF_2') | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.88/1.17  tff(c_89, plain, (![B_36]: (~v3_tex_2('#skF_1'('#skF_2', B_36), '#skF_2') | ~v2_tex_2(B_36, '#skF_2') | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_78, c_18])).
% 1.88/1.17  tff(c_98, plain, (![B_36]: (~v3_tex_2('#skF_1'('#skF_2', B_36), '#skF_2') | ~v2_tex_2(B_36, '#skF_2') | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_89])).
% 1.88/1.17  tff(c_101, plain, (![B_37]: (~v3_tex_2('#skF_1'('#skF_2', B_37), '#skF_2') | ~v2_tex_2(B_37, '#skF_2') | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_26, c_98])).
% 1.88/1.17  tff(c_115, plain, (![A_38]: (~v3_tex_2('#skF_1'('#skF_2', A_38), '#skF_2') | ~v2_tex_2(A_38, '#skF_2') | ~r1_tarski(A_38, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_101])).
% 1.88/1.17  tff(c_119, plain, (![A_2]: (~v2_tex_2(A_2, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_2, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_65, c_115])).
% 1.88/1.17  tff(c_122, plain, (![A_2]: (~v2_tex_2(A_2, '#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_2, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_119])).
% 1.88/1.17  tff(c_124, plain, (![A_39]: (~v2_tex_2(A_39, '#skF_2') | ~r1_tarski(A_39, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_26, c_122])).
% 1.88/1.17  tff(c_129, plain, (~v2_tex_2(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_4, c_124])).
% 1.88/1.17  tff(c_132, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_59, c_129])).
% 1.88/1.17  tff(c_135, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_132])).
% 1.88/1.17  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_135])).
% 1.88/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  Inference rules
% 1.88/1.17  ----------------------
% 1.88/1.17  #Ref     : 0
% 1.88/1.17  #Sup     : 18
% 1.88/1.17  #Fact    : 0
% 1.88/1.17  #Define  : 0
% 1.88/1.17  #Split   : 0
% 1.88/1.17  #Chain   : 0
% 1.88/1.17  #Close   : 0
% 1.88/1.17  
% 1.88/1.17  Ordering : KBO
% 1.88/1.17  
% 1.88/1.17  Simplification rules
% 1.88/1.17  ----------------------
% 1.88/1.17  #Subsume      : 1
% 1.88/1.17  #Demod        : 13
% 1.88/1.17  #Tautology    : 2
% 1.88/1.17  #SimpNegUnit  : 4
% 1.88/1.17  #BackRed      : 0
% 1.88/1.17  
% 1.88/1.17  #Partial instantiations: 0
% 1.88/1.17  #Strategies tried      : 1
% 1.88/1.17  
% 1.88/1.17  Timing (in seconds)
% 1.88/1.17  ----------------------
% 1.97/1.17  Preprocessing        : 0.26
% 1.97/1.17  Parsing              : 0.15
% 1.97/1.17  CNF conversion       : 0.02
% 1.97/1.17  Main loop            : 0.16
% 1.97/1.17  Inferencing          : 0.07
% 1.97/1.17  Reduction            : 0.04
% 1.97/1.17  Demodulation         : 0.03
% 1.97/1.17  BG Simplification    : 0.01
% 1.97/1.17  Subsumption          : 0.03
% 1.97/1.17  Abstraction          : 0.01
% 1.97/1.17  MUC search           : 0.00
% 1.97/1.17  Cooper               : 0.00
% 1.97/1.17  Total                : 0.46
% 1.97/1.17  Index Insertion      : 0.00
% 1.97/1.17  Index Deletion       : 0.00
% 1.97/1.17  Index Matching       : 0.00
% 1.97/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
