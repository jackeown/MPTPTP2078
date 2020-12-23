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
% DateTime   : Thu Dec  3 10:20:29 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    5
%              Number of atoms          :   74 ( 160 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v3_pre_topc(B,A)
                    & v3_pre_topc(C,A) )
                 => v3_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_59,plain,(
    ! [B_29,A_30] :
      ( r2_hidden(B_29,u1_pre_topc(A_30))
      | ~ v3_pre_topc(B_29,A_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_66,plain,
    ( r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_59])).

tff(c_73,plain,(
    r2_hidden('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_66])).

tff(c_46,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_69,plain,
    ( r2_hidden('#skF_6',u1_pre_topc('#skF_4'))
    | ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_59])).

tff(c_76,plain,(
    r2_hidden('#skF_6',u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_69])).

tff(c_187,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_59),B_60,C_61),u1_pre_topc(A_59))
      | ~ r2_hidden(C_61,u1_pre_topc(A_59))
      | ~ r2_hidden(B_60,u1_pre_topc(A_59))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ v2_pre_topc(A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( m1_subset_1(k9_subset_1(A_1,B_2,C_3),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [B_31,A_32] :
      ( v3_pre_topc(B_31,A_32)
      | ~ r2_hidden(B_31,u1_pre_topc(A_32))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_88,plain,(
    ! [A_32,B_2,C_3] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(A_32),B_2,C_3),A_32)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(A_32),B_2,C_3),u1_pre_topc(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(u1_struct_0(A_32))) ) ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_207,plain,(
    ! [A_62,B_63,C_64] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(A_62),B_63,C_64),A_62)
      | ~ r2_hidden(C_64,u1_pre_topc(A_62))
      | ~ r2_hidden(B_63,u1_pre_topc(A_62))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ v2_pre_topc(A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_187,c_88])).

tff(c_44,plain,(
    ~ v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_214,plain,
    ( ~ r2_hidden('#skF_6',u1_pre_topc('#skF_4'))
    | ~ r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_207,c_44])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_52,c_50,c_73,c_76,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:14:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.32  
% 2.41/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.32  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3
% 2.41/1.32  
% 2.41/1.32  %Foreground sorts:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Background operators:
% 2.41/1.32  
% 2.41/1.32  
% 2.41/1.32  %Foreground operators:
% 2.41/1.32  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.41/1.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.41/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.41/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.41/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.32  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.32  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.41/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.41/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.32  
% 2.71/1.33  tff(f_80, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_pre_topc(C, A)) => v3_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_1)).
% 2.71/1.33  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.71/1.33  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.71/1.33  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.71/1.33  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.33  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.33  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.33  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.33  tff(c_48, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.33  tff(c_59, plain, (![B_29, A_30]: (r2_hidden(B_29, u1_pre_topc(A_30)) | ~v3_pre_topc(B_29, A_30) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.33  tff(c_66, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_59])).
% 2.71/1.33  tff(c_73, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_66])).
% 2.71/1.33  tff(c_46, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.33  tff(c_69, plain, (r2_hidden('#skF_6', u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_59])).
% 2.71/1.33  tff(c_76, plain, (r2_hidden('#skF_6', u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_69])).
% 2.71/1.33  tff(c_187, plain, (![A_59, B_60, C_61]: (r2_hidden(k9_subset_1(u1_struct_0(A_59), B_60, C_61), u1_pre_topc(A_59)) | ~r2_hidden(C_61, u1_pre_topc(A_59)) | ~r2_hidden(B_60, u1_pre_topc(A_59)) | ~m1_subset_1(C_61, k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~v2_pre_topc(A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.71/1.33  tff(c_2, plain, (![A_1, B_2, C_3]: (m1_subset_1(k9_subset_1(A_1, B_2, C_3), k1_zfmisc_1(A_1)) | ~m1_subset_1(C_3, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.71/1.33  tff(c_77, plain, (![B_31, A_32]: (v3_pre_topc(B_31, A_32) | ~r2_hidden(B_31, u1_pre_topc(A_32)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.33  tff(c_88, plain, (![A_32, B_2, C_3]: (v3_pre_topc(k9_subset_1(u1_struct_0(A_32), B_2, C_3), A_32) | ~r2_hidden(k9_subset_1(u1_struct_0(A_32), B_2, C_3), u1_pre_topc(A_32)) | ~l1_pre_topc(A_32) | ~m1_subset_1(C_3, k1_zfmisc_1(u1_struct_0(A_32))))), inference(resolution, [status(thm)], [c_2, c_77])).
% 2.71/1.33  tff(c_207, plain, (![A_62, B_63, C_64]: (v3_pre_topc(k9_subset_1(u1_struct_0(A_62), B_63, C_64), A_62) | ~r2_hidden(C_64, u1_pre_topc(A_62)) | ~r2_hidden(B_63, u1_pre_topc(A_62)) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~v2_pre_topc(A_62) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_187, c_88])).
% 2.71/1.33  tff(c_44, plain, (~v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.71/1.33  tff(c_214, plain, (~r2_hidden('#skF_6', u1_pre_topc('#skF_4')) | ~r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_207, c_44])).
% 2.71/1.33  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_52, c_50, c_73, c_76, c_214])).
% 2.71/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.33  
% 2.71/1.33  Inference rules
% 2.71/1.33  ----------------------
% 2.71/1.33  #Ref     : 0
% 2.71/1.33  #Sup     : 28
% 2.71/1.33  #Fact    : 0
% 2.71/1.33  #Define  : 0
% 2.71/1.33  #Split   : 0
% 2.71/1.33  #Chain   : 0
% 2.71/1.33  #Close   : 0
% 2.71/1.33  
% 2.71/1.33  Ordering : KBO
% 2.71/1.33  
% 2.71/1.33  Simplification rules
% 2.71/1.33  ----------------------
% 2.71/1.33  #Subsume      : 2
% 2.71/1.33  #Demod        : 16
% 2.71/1.33  #Tautology    : 15
% 2.71/1.33  #SimpNegUnit  : 0
% 2.71/1.33  #BackRed      : 0
% 2.71/1.33  
% 2.71/1.33  #Partial instantiations: 0
% 2.71/1.33  #Strategies tried      : 1
% 2.71/1.33  
% 2.71/1.33  Timing (in seconds)
% 2.71/1.33  ----------------------
% 2.71/1.34  Preprocessing        : 0.31
% 2.71/1.34  Parsing              : 0.17
% 2.71/1.34  CNF conversion       : 0.02
% 2.71/1.34  Main loop            : 0.23
% 2.71/1.34  Inferencing          : 0.10
% 2.71/1.34  Reduction            : 0.06
% 2.71/1.34  Demodulation         : 0.04
% 2.71/1.34  BG Simplification    : 0.02
% 2.71/1.34  Subsumption          : 0.05
% 2.71/1.34  Abstraction          : 0.01
% 2.71/1.34  MUC search           : 0.00
% 2.71/1.34  Cooper               : 0.00
% 2.71/1.34  Total                : 0.57
% 2.71/1.34  Index Insertion      : 0.00
% 2.71/1.34  Index Deletion       : 0.00
% 2.71/1.34  Index Matching       : 0.00
% 2.71/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
