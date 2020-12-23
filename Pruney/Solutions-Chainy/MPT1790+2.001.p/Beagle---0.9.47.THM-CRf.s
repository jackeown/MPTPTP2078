%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:49 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  98 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 275 expanded)
%              Number of equality atoms :    8 (  36 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A,B))))
               => ( C = B
                 => v3_pre_topc(C,k6_tmap_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    '#skF_2' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_31,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_157,plain,(
    ! [B_32,A_33] :
      ( r2_hidden(B_32,k5_tmap_1(A_33,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_161,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_157])).

tff(c_167,plain,
    ( r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_161])).

tff(c_168,plain,(
    r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_167])).

tff(c_223,plain,(
    ! [A_36,B_37] :
      ( u1_pre_topc(k6_tmap_1(A_36,B_37)) = k5_tmap_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_229,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) = k5_tmap_1('#skF_1','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_223])).

tff(c_234,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) = k5_tmap_1('#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_229])).

tff(c_235,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) = k5_tmap_1('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_234])).

tff(c_18,plain,(
    ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_33,plain,(
    ~ v3_pre_topc('#skF_3',k6_tmap_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_50,plain,(
    ! [B_18,A_19] :
      ( v3_pre_topc(B_18,A_19)
      | ~ r2_hidden(B_18,u1_pre_topc(A_19))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_53,plain,
    ( v3_pre_topc('#skF_3',k6_tmap_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_3',u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_50])).

tff(c_59,plain,
    ( ~ r2_hidden('#skF_3',u1_pre_topc(k6_tmap_1('#skF_1','#skF_3')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_53])).

tff(c_64,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_65,plain,(
    ! [A_20,B_21] :
      ( l1_pre_topc(k6_tmap_1(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_71,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_65])).

tff(c_75,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_71])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_64,c_75])).

tff(c_78,plain,(
    ~ r2_hidden('#skF_3',u1_pre_topc(k6_tmap_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_236,plain,(
    ~ r2_hidden('#skF_3',k5_tmap_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_78])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:55:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.28  
% 1.97/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.28  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.97/1.28  
% 1.97/1.28  %Foreground sorts:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Background operators:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Foreground operators:
% 1.97/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.97/1.28  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.97/1.28  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.97/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.28  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.97/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.28  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.97/1.28  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 1.97/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.97/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.28  
% 2.19/1.29  tff(f_93, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A, B)))) => ((C = B) => v3_pre_topc(C, k6_tmap_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tmap_1)).
% 2.19/1.29  tff(f_61, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tmap_1)).
% 2.19/1.29  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.19/1.29  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.19/1.29  tff(f_49, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 2.19/1.29  tff(c_30, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.19/1.29  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.19/1.29  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.19/1.29  tff(c_20, plain, ('#skF_2'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.19/1.29  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.19/1.29  tff(c_31, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 2.19/1.29  tff(c_157, plain, (![B_32, A_33]: (r2_hidden(B_32, k5_tmap_1(A_33, B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.19/1.29  tff(c_161, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_31, c_157])).
% 2.19/1.29  tff(c_167, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_1', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_161])).
% 2.19/1.29  tff(c_168, plain, (r2_hidden('#skF_3', k5_tmap_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_167])).
% 2.19/1.29  tff(c_223, plain, (![A_36, B_37]: (u1_pre_topc(k6_tmap_1(A_36, B_37))=k5_tmap_1(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.19/1.29  tff(c_229, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_3'))=k5_tmap_1('#skF_1', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_31, c_223])).
% 2.19/1.29  tff(c_234, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_3'))=k5_tmap_1('#skF_1', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_229])).
% 2.19/1.29  tff(c_235, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_3'))=k5_tmap_1('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_234])).
% 2.19/1.29  tff(c_18, plain, (~v3_pre_topc('#skF_3', k6_tmap_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.19/1.29  tff(c_33, plain, (~v3_pre_topc('#skF_3', k6_tmap_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18])).
% 2.19/1.29  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.19/1.29  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.19/1.29  tff(c_50, plain, (![B_18, A_19]: (v3_pre_topc(B_18, A_19) | ~r2_hidden(B_18, u1_pre_topc(A_19)) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.29  tff(c_53, plain, (v3_pre_topc('#skF_3', k6_tmap_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_3', u1_pre_topc(k6_tmap_1('#skF_1', '#skF_3'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_50])).
% 2.19/1.29  tff(c_59, plain, (~r2_hidden('#skF_3', u1_pre_topc(k6_tmap_1('#skF_1', '#skF_3'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_33, c_53])).
% 2.19/1.29  tff(c_64, plain, (~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_59])).
% 2.19/1.29  tff(c_65, plain, (![A_20, B_21]: (l1_pre_topc(k6_tmap_1(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.29  tff(c_71, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_31, c_65])).
% 2.19/1.29  tff(c_75, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_71])).
% 2.19/1.29  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_64, c_75])).
% 2.19/1.29  tff(c_78, plain, (~r2_hidden('#skF_3', u1_pre_topc(k6_tmap_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_59])).
% 2.19/1.29  tff(c_236, plain, (~r2_hidden('#skF_3', k5_tmap_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_78])).
% 2.19/1.29  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_236])).
% 2.19/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  Inference rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Ref     : 0
% 2.19/1.29  #Sup     : 33
% 2.19/1.29  #Fact    : 0
% 2.19/1.29  #Define  : 0
% 2.19/1.29  #Split   : 4
% 2.19/1.29  #Chain   : 0
% 2.19/1.29  #Close   : 0
% 2.19/1.29  
% 2.19/1.29  Ordering : KBO
% 2.19/1.29  
% 2.19/1.29  Simplification rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Subsume      : 4
% 2.19/1.29  #Demod        : 65
% 2.19/1.29  #Tautology    : 17
% 2.19/1.29  #SimpNegUnit  : 11
% 2.19/1.29  #BackRed      : 2
% 2.19/1.29  
% 2.19/1.29  #Partial instantiations: 0
% 2.19/1.29  #Strategies tried      : 1
% 2.19/1.29  
% 2.19/1.29  Timing (in seconds)
% 2.19/1.29  ----------------------
% 2.19/1.30  Preprocessing        : 0.28
% 2.19/1.30  Parsing              : 0.15
% 2.19/1.30  CNF conversion       : 0.02
% 2.19/1.30  Main loop            : 0.18
% 2.19/1.30  Inferencing          : 0.06
% 2.19/1.30  Reduction            : 0.07
% 2.19/1.30  Demodulation         : 0.05
% 2.19/1.30  BG Simplification    : 0.01
% 2.19/1.30  Subsumption          : 0.03
% 2.19/1.30  Abstraction          : 0.01
% 2.19/1.30  MUC search           : 0.00
% 2.19/1.30  Cooper               : 0.00
% 2.19/1.30  Total                : 0.50
% 2.19/1.30  Index Insertion      : 0.00
% 2.19/1.30  Index Deletion       : 0.00
% 2.19/1.30  Index Matching       : 0.00
% 2.19/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
