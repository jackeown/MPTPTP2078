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
% DateTime   : Thu Dec  3 10:29:50 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   46 (  98 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 280 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_6] :
      ( m1_pre_topc(A_6,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( m1_subset_1(u1_struct_0(B_5),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_28])).

tff(c_44,plain,(
    ! [C_31,A_32,B_33] :
      ( v2_tex_2(C_31,A_32)
      | ~ v2_tex_2(B_33,A_32)
      | ~ r1_tarski(C_31,B_33)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_51,plain,(
    ! [A_34] :
      ( v2_tex_2('#skF_2',A_34)
      | ~ v2_tex_2(u1_struct_0('#skF_1'),A_34)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_32,c_44])).

tff(c_61,plain,(
    ! [A_35] :
      ( v2_tex_2('#skF_2',A_35)
      | ~ v2_tex_2(u1_struct_0('#skF_1'),A_35)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc('#skF_1',A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_67,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_61])).

tff(c_71,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_67])).

tff(c_72,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_71])).

tff(c_82,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_85,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_85])).

tff(c_91,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_22,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_73,plain,(
    ! [B_36,A_37] :
      ( v2_tex_2(u1_struct_0(B_36),A_37)
      | ~ v1_tdlat_3(B_36)
      | ~ m1_subset_1(u1_struct_0(B_36),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_pre_topc(B_36,A_37)
      | v2_struct_0(B_36)
      | ~ l1_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    ! [B_38,A_39] :
      ( v2_tex_2(u1_struct_0(B_38),A_39)
      | ~ v1_tdlat_3(B_38)
      | v2_struct_0(B_38)
      | v2_struct_0(A_39)
      | ~ m1_pre_topc(B_38,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_90,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_95,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_92,c_90])).

tff(c_98,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_91,c_22,c_95])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:04:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  %$ v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.70/1.15  
% 1.70/1.15  %Foreground sorts:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Background operators:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Foreground operators:
% 1.70/1.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.70/1.15  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 1.70/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.15  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.70/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.15  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.70/1.15  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.70/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.70/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.15  
% 1.70/1.16  tff(f_89, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 1.70/1.16  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 1.70/1.16  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 1.70/1.16  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.70/1.16  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 1.70/1.16  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 1.70/1.16  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.70/1.16  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.70/1.16  tff(c_8, plain, (![A_6]: (m1_pre_topc(A_6, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.70/1.16  tff(c_16, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.70/1.16  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.70/1.16  tff(c_6, plain, (![B_5, A_3]: (m1_subset_1(u1_struct_0(B_5), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.70/1.16  tff(c_28, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.16  tff(c_32, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_28])).
% 1.70/1.16  tff(c_44, plain, (![C_31, A_32, B_33]: (v2_tex_2(C_31, A_32) | ~v2_tex_2(B_33, A_32) | ~r1_tarski(C_31, B_33) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.70/1.16  tff(c_51, plain, (![A_34]: (v2_tex_2('#skF_2', A_34) | ~v2_tex_2(u1_struct_0('#skF_1'), A_34) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_32, c_44])).
% 1.70/1.16  tff(c_61, plain, (![A_35]: (v2_tex_2('#skF_2', A_35) | ~v2_tex_2(u1_struct_0('#skF_1'), A_35) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc('#skF_1', A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_6, c_51])).
% 1.70/1.16  tff(c_67, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_61])).
% 1.70/1.16  tff(c_71, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_67])).
% 1.70/1.16  tff(c_72, plain, (~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_16, c_71])).
% 1.70/1.16  tff(c_82, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_72])).
% 1.70/1.16  tff(c_85, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_82])).
% 1.70/1.16  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_85])).
% 1.70/1.16  tff(c_91, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 1.70/1.16  tff(c_22, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.70/1.16  tff(c_73, plain, (![B_36, A_37]: (v2_tex_2(u1_struct_0(B_36), A_37) | ~v1_tdlat_3(B_36) | ~m1_subset_1(u1_struct_0(B_36), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_pre_topc(B_36, A_37) | v2_struct_0(B_36) | ~l1_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.70/1.16  tff(c_92, plain, (![B_38, A_39]: (v2_tex_2(u1_struct_0(B_38), A_39) | ~v1_tdlat_3(B_38) | v2_struct_0(B_38) | v2_struct_0(A_39) | ~m1_pre_topc(B_38, A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_6, c_73])).
% 1.70/1.16  tff(c_90, plain, (~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 1.70/1.16  tff(c_95, plain, (~v1_tdlat_3('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_92, c_90])).
% 1.70/1.16  tff(c_98, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_91, c_22, c_95])).
% 1.70/1.16  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_98])).
% 1.70/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  Inference rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Ref     : 0
% 1.70/1.16  #Sup     : 13
% 1.70/1.16  #Fact    : 0
% 1.70/1.16  #Define  : 0
% 1.70/1.16  #Split   : 1
% 1.70/1.16  #Chain   : 0
% 1.70/1.16  #Close   : 0
% 1.70/1.16  
% 1.70/1.16  Ordering : KBO
% 1.70/1.16  
% 1.70/1.16  Simplification rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Subsume      : 1
% 1.70/1.16  #Demod        : 5
% 1.70/1.16  #Tautology    : 1
% 1.70/1.16  #SimpNegUnit  : 2
% 1.70/1.16  #BackRed      : 0
% 1.70/1.16  
% 1.70/1.16  #Partial instantiations: 0
% 1.70/1.16  #Strategies tried      : 1
% 1.70/1.16  
% 1.70/1.16  Timing (in seconds)
% 1.70/1.16  ----------------------
% 1.70/1.16  Preprocessing        : 0.27
% 1.70/1.16  Parsing              : 0.15
% 1.70/1.16  CNF conversion       : 0.02
% 1.70/1.16  Main loop            : 0.14
% 1.70/1.16  Inferencing          : 0.05
% 1.70/1.16  Reduction            : 0.03
% 1.70/1.16  Demodulation         : 0.03
% 1.70/1.16  BG Simplification    : 0.01
% 1.70/1.16  Subsumption          : 0.03
% 1.70/1.16  Abstraction          : 0.01
% 1.70/1.16  MUC search           : 0.00
% 1.70/1.16  Cooper               : 0.00
% 1.70/1.16  Total                : 0.44
% 1.70/1.16  Index Insertion      : 0.00
% 1.70/1.16  Index Deletion       : 0.00
% 1.70/1.16  Index Matching       : 0.00
% 1.70/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
