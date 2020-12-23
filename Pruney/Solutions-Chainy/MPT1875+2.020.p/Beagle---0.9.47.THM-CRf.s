%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:49 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 125 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_31,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_14,plain,(
    ! [A_12] :
      ( v2_tex_2(u1_struct_0(A_12),A_12)
      | ~ v1_tdlat_3(A_12)
      | ~ m1_subset_1(u1_struct_0(A_12),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_35,plain,(
    ! [A_12] :
      ( v2_tex_2(u1_struct_0(A_12),A_12)
      | ~ v1_tdlat_3(A_12)
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_14])).

tff(c_20,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [C_34,A_35,B_36] :
      ( r2_hidden(C_34,A_35)
      | ~ r2_hidden(C_34,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_44,B_45,A_46] :
      ( r2_hidden('#skF_1'(A_44,B_45),A_46)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(A_46))
      | r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_47,A_48] :
      ( ~ m1_subset_1(A_47,k1_zfmisc_1(A_48))
      | r1_tarski(A_47,A_48) ) ),
    inference(resolution,[status(thm)],[c_84,c_4])).

tff(c_103,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_96])).

tff(c_18,plain,(
    ! [C_21,A_15,B_19] :
      ( v2_tex_2(C_21,A_15)
      | ~ v2_tex_2(B_19,A_15)
      | ~ r1_tarski(C_21,B_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_199,plain,(
    ! [A_72] :
      ( v2_tex_2('#skF_3',A_72)
      | ~ v2_tex_2(u1_struct_0('#skF_2'),A_72)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_103,c_18])).

tff(c_203,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_31,c_199])).

tff(c_206,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_203])).

tff(c_207,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_206])).

tff(c_210,plain,
    ( ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_35,c_207])).

tff(c_213,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_210])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n015.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:46:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.37  
% 2.19/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.38  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.38  
% 2.19/1.38  %Foreground sorts:
% 2.19/1.38  
% 2.19/1.38  
% 2.19/1.38  %Background operators:
% 2.19/1.38  
% 2.19/1.38  
% 2.19/1.38  %Foreground operators:
% 2.19/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.19/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.19/1.38  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.19/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.38  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.19/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.19/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.19/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.38  
% 2.49/1.39  tff(f_86, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 2.49/1.39  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.49/1.39  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.49/1.39  tff(f_57, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 2.49/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.49/1.39  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.49/1.39  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 2.49/1.39  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.49/1.39  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.49/1.39  tff(c_26, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.49/1.39  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.49/1.39  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.49/1.39  tff(c_31, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.49/1.39  tff(c_14, plain, (![A_12]: (v2_tex_2(u1_struct_0(A_12), A_12) | ~v1_tdlat_3(A_12) | ~m1_subset_1(u1_struct_0(A_12), k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.49/1.39  tff(c_35, plain, (![A_12]: (v2_tex_2(u1_struct_0(A_12), A_12) | ~v1_tdlat_3(A_12) | ~l1_pre_topc(A_12) | v2_struct_0(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_14])).
% 2.49/1.39  tff(c_20, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.49/1.39  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.49/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.39  tff(c_59, plain, (![C_34, A_35, B_36]: (r2_hidden(C_34, A_35) | ~r2_hidden(C_34, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.49/1.39  tff(c_84, plain, (![A_44, B_45, A_46]: (r2_hidden('#skF_1'(A_44, B_45), A_46) | ~m1_subset_1(A_44, k1_zfmisc_1(A_46)) | r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_6, c_59])).
% 2.49/1.39  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.39  tff(c_96, plain, (![A_47, A_48]: (~m1_subset_1(A_47, k1_zfmisc_1(A_48)) | r1_tarski(A_47, A_48))), inference(resolution, [status(thm)], [c_84, c_4])).
% 2.49/1.39  tff(c_103, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_96])).
% 2.49/1.39  tff(c_18, plain, (![C_21, A_15, B_19]: (v2_tex_2(C_21, A_15) | ~v2_tex_2(B_19, A_15) | ~r1_tarski(C_21, B_19) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.49/1.39  tff(c_199, plain, (![A_72]: (v2_tex_2('#skF_3', A_72) | ~v2_tex_2(u1_struct_0('#skF_2'), A_72) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_103, c_18])).
% 2.49/1.39  tff(c_203, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_31, c_199])).
% 2.49/1.39  tff(c_206, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_203])).
% 2.49/1.39  tff(c_207, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_20, c_206])).
% 2.49/1.39  tff(c_210, plain, (~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_35, c_207])).
% 2.49/1.39  tff(c_213, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_210])).
% 2.49/1.39  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_213])).
% 2.49/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.39  
% 2.49/1.39  Inference rules
% 2.49/1.39  ----------------------
% 2.49/1.39  #Ref     : 0
% 2.49/1.39  #Sup     : 42
% 2.49/1.39  #Fact    : 0
% 2.49/1.39  #Define  : 0
% 2.49/1.39  #Split   : 0
% 2.49/1.39  #Chain   : 0
% 2.49/1.39  #Close   : 0
% 2.49/1.39  
% 2.49/1.39  Ordering : KBO
% 2.49/1.39  
% 2.49/1.39  Simplification rules
% 2.49/1.39  ----------------------
% 2.49/1.39  #Subsume      : 7
% 2.49/1.39  #Demod        : 8
% 2.49/1.39  #Tautology    : 6
% 2.49/1.39  #SimpNegUnit  : 2
% 2.49/1.39  #BackRed      : 0
% 2.49/1.39  
% 2.49/1.39  #Partial instantiations: 0
% 2.49/1.39  #Strategies tried      : 1
% 2.49/1.39  
% 2.49/1.39  Timing (in seconds)
% 2.49/1.39  ----------------------
% 2.49/1.39  Preprocessing        : 0.37
% 2.49/1.39  Parsing              : 0.23
% 2.49/1.39  CNF conversion       : 0.02
% 2.49/1.39  Main loop            : 0.24
% 2.49/1.39  Inferencing          : 0.09
% 2.49/1.39  Reduction            : 0.06
% 2.49/1.39  Demodulation         : 0.04
% 2.49/1.39  BG Simplification    : 0.01
% 2.49/1.39  Subsumption          : 0.06
% 2.49/1.39  Abstraction          : 0.01
% 2.49/1.39  MUC search           : 0.00
% 2.49/1.39  Cooper               : 0.00
% 2.49/1.39  Total                : 0.64
% 2.49/1.39  Index Insertion      : 0.00
% 2.49/1.39  Index Deletion       : 0.00
% 2.49/1.39  Index Matching       : 0.00
% 2.49/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
